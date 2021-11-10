#! /usr/bin/env python3
# Copyright 2021 OVHCloud
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

import argparse
import collections
import functools
import math
from typing import List, DefaultDict, Set, Tuple, Dict
import xml.etree.ElementTree as ET
import subprocess

import libvirt
import pyparsing as pp
import sympy as sm

# 😱
# Sorry, this parser is bugged and very poorly written, but it seems to work
# well enough for our use-case.


def mask_to_range(n, mask, width=None):
    # Turn a masked number into a range
    width = round(math.log2(mask))
    return n, n | (mask ^ (2**width - 1))


def generate_openflow_grammar():
    s = pp.Suppress
    w = pp.Word
    group = pp.Group

    LPAR = s('(')
    RPAR = s(')')
    LBRACKET = s('[')
    RBRACKET = s(']')

    DEC_NUMBER = pp.Regex(r'[0-9]+').setParseAction(lambda t: int(t[0]))
    HEX_NUMBER = pp.Regex(
        r'0x[0-9A-Fa-f]+'
    ).setParseAction(lambda t: int(t[0], 16))

    NUMBER = (HEX_NUMBER | DEC_NUMBER)
    EXPRESSION = pp.Forward()
    MASKED_NUMBER = ((NUMBER + s("/") + NUMBER)
                     .setParseAction(lambda t: mask_to_range(t[0], t[1])))

    INDEXER = LBRACKET + pp.Optional(w(pp.alphanums + ".")) + RBRACKET
    IDENTIFIER = w(pp.alphas, pp.alphanums + "_")

    KV_PAIR = (IDENTIFIER("key") + s("=") +
               (NUMBER ^ MASKED_NUMBER ^ EXPRESSION)("value"))

    FLOW_KV_SEP = s(", ") | s(",") | s(" ")
    PROTOCOL = pp.oneOf("eth ip ipv6 icmp icmp6 tcp tcp6 udp udp6 "
                        "sctp sctp6 arp rarp mpls mplsm")

    FLOW_FILTER_FIELDS = (
        PROTOCOL("proto") |
        (s("out_port=") + NUMBER("out_port")) |
        (s("vlan_tci=") + NUMBER("vlan_tci")) |
        (s("dl_vlan=") + NUMBER("dl_vlan"))
    )
    ACTION_LOAD = group(s('load:') + (
                        HEX_NUMBER('value') + s('->') + IDENTIFIER('key') +
                        INDEXER('index')))("load")

    FLOW_KV = pp.Dict(group(~s('action') + (KV_PAIR | IDENTIFIER)))

    FUNC_ARG = (FLOW_KV ^ EXPRESSION | pp.Empty()).setName('param')
    FUNC_CALL = group(
        IDENTIFIER('func_name') + LPAR +
        group(pp.delimitedList(FUNC_ARG, delim=FLOW_KV_SEP))('func_param') +
        RPAR)('func_call')

    EXPRESSION <<= (FUNC_CALL |
                    (IDENTIFIER + INDEXER) |
                    pp.QuotedString('"') | ACTION_LOAD |
                    (NUMBER ^ w(pp.alphanums + "+:_/-.")))

    ACTION_RESUBMIT = group((
        s("resubmit:") + EXPRESSION("resubmit_port")) | (
            s("resubmit") + LPAR +
            pp.Optional(EXPRESSION("resubmit_port")) + s(",") +
            pp.Optional(EXPRESSION("resubmit_table")
                        .setParseAction(lambda t: int(t[0]))) + RPAR
    ))("resubmit")

    KW_ACTION = pp.Dict(group(IDENTIFIER + s(":") + EXPRESSION))

    ACTION_CONJUNCTION = group(
        s("conjunction") + LPAR +
        DEC_NUMBER("conj_id").setParseAction(lambda t: int(t[0])) + s(',') +
        DEC_NUMBER("conj_k").setParseAction(lambda t: int(t[0])) + s("/") +
        DEC_NUMBER("conj_n").setParseAction(lambda t: int(t[0])) + RPAR
    )("conjunction")

    ACTION = group(ACTION_LOAD | ACTION_RESUBMIT | ACTION_CONJUNCTION |
                   KW_ACTION | FUNC_CALL | IDENTIFIER('action_type'))
    COLOR_MARKER = pp.Regex(r'\x1b\[((\d|\d;)*m|K)')
    FLOW_LINE = (group(pp.delimitedList(
                        pp.Optional(FLOW_FILTER_FIELDS ^ FLOW_KV),
                        delim=FLOW_KV_SEP))("fields") -
                 pp.Optional(FLOW_KV_SEP) - s("actions=") -
                 group(
                     pp.delimitedList(ACTION, delim=FLOW_KV_SEP)
                 )("actions")).ignore(COLOR_MARKER)

    return FLOW_LINE


# Fields we don't care about when checking whether a cursor exhausted a rule
MISC_FIELDS = ['cookie', 'table', 'conj_id', 'priority']


flow_grammar = generate_openflow_grammar()


def human_rule_sorter(r):
    """
    A function to help sort rules for human consumption.

    The idea here is to group rules by tables, priority, conjunction and port.
    """

    conjunctions = []

    dst_port = (r.fields.tp_dst if isinstance(r.fields.tp_dst, tuple)
                else (r.fields.tp_dst or 0, r.fields.tp_dst or 0))

    sort_keys = [r.table if r.table
                 else 0, -r.priority, conjunctions, dst_port]

    for action in r.actions:
        conj = action.conjunction
        if conj:
            conjunctions.append((-1 * conj.conj_id, conj.conj_k))
        conj_id = int(r.fields.get('conj_id', 0))
        if conj_id:
            conjunctions.insert(0, (-1 * conj_id, 99))

    conjunctions.sort()
    return sort_keys


class FlowCursor:

    def __init__(self):
        self.fields = collections.defaultdict(lambda: 0)
        self.from_rule = None

    def copy(self):
        a = FlowCursor()
        a.fields = self.fields.copy()
        return a


def close_intervals(expr):
    """Turns Interval.open into Interval, they are nicer to look at."""

    return expr.replace(
        lambda s: s.is_Interval,
        lambda i: sm.Interval(i.args[0]+1, i.args[1]-1),
        simultaneous=False
    )


class FlowRule:

    def __init__(self):
        self.annotations = dict()
        self._conj_key = None
        self._accumulated_conditions = True
        self._parent_rules: Set[Tuple['FlowRule']] = set()
        self._ranges = {}
        self._dump: FlowDump = None

    @property
    def simplified_conditions(self):
        conjunction_conditions = True
        if self.fields.conj_id:
            conj_precursors = self._dump.conj_setters[self.fields.conj_id]
            for rules in conj_precursors.values():
                ored = self._dump.rules_conditions_union(rules)
                conjunction_conditions &= ored

        intrinsic = self.intrinsic_conditions()
        return (self._accumulated_conditions &
                intrinsic & conjunction_conditions)

    @property
    def conditions(self):
        return self._accumulated_conditions & self.intrinsic_conditions()

    @classmethod
    def from_line(cls, line, dump):
        self = cls()
        self._line = line
        self._dump = dump
        try:
            parse_out = flow_grammar.parseString(line, True)
        except Exception as excp:
            print("Error parsing line")
            print(line)
            raise excp

        self.priority = parse_out.fields.get('priority', 32768)
        self.table = parse_out.fields.get('table')
        self.actions = parse_out.actions
        self.fields = parse_out.fields
        self.fields = parse_out.fields
        return self

    def pass_or_drop(self):
        for action in self.actions:
            if action.getName() == 'action_type':
                if action.action_type == 'drop':
                    return 'drop'
            if action.action_type in ("NORMAL", ):
                    return 'pass'
            if action.getName() == 'output':
                return 'pass'
        return None

    @functools.lru_cache(256)
    def intrinsic_conditions(self):
        """
        Returns the intrinsic conditions of a flow rule.

        That is, the conditions set by the rule itself represented
        as a sympy expression, with ranges "simplified" out.
        """

        def to_port_annotation(parsed):
            # convert both single port and ranges into sympy.Interval
            # (open intervals)
            if isinstance(parsed, int):
                rv = sm.Interval(parsed-1, parsed+1, True, True)
            else:
                rv = sm.Interval(parsed[0]-1, parsed[1]+1, True, True)
            return rv

        annotation_fields_conversions = {
            'tp_dst': ('dest_port', to_port_annotation),
            'tp_src': ('src_port', to_port_annotation),
            'dl_src': ('src_mac', sm.Symbol),
            'nw_src': ('source_ip', sm.Symbol),
            'ipv6_src': ('source_ip6', sm.Symbol),
            'nd_target': ('dest_ip6', sm.Symbol),
            'nw_dst': ('dest_ip', sm.Symbol),
            'proto': ('proto', sm.Symbol),
            'ct_state': ('ct_state', sm.Symbol)
        }

        conds = []

        for fn, (dst, conv) in annotation_fields_conversions.items():
            if self.fields.get(fn):
                value = conv(self.fields[fn]) if conv else self.fields[fn]
                if isinstance(value, sm.Interval):
                    # I know it's not super cool to lru_cache this function
                    # but in this case I don't think it's going to cause
                    # much trouble ...
                    self._ranges["__range_" + dst] = value
                    conds.append(sm.Symbol("__range_" + dst))
                else:
                    cond = sm.Eq(sm.Symbol(dst), value)
                    conds.append(cond)
        return sm.And(*conds)

    def passes_cursor(self, cursor: FlowCursor) -> Tuple[
            FlowCursor, List['FlowRule'], bool]:
        """
        Runs cursor through the rule. If the rule passes,
        return a copy of cursor modified to reflect the changes applied
        by the rule, along with a list rules this one branches to and
        whether the cursor exhausted all the rule's matches.

        Additionally, if the rule is an interesting exit node of the rule
        graph (has action output or NORMAL), it registers the rule in the
        dump's output_nodes dict for later use in the summary.
        """

        rule_fields_count = sum(k not in MISC_FIELDS
                                for k in self.fields.asDict().keys()) or -1
        cursor_fields_count = len(cursor.fields)
        for field_name, v in self.fields.asDict().items():
            if field_name in cursor.fields:
                if v != cursor.fields[field_name]:
                    # We met a field that doesn't match what we currently have
                    # in the cursor, so this rule doesn't pass
                    return None, [], False
                else:
                    rule_fields_count -= 1
                    cursor_fields_count -= 1

        next_rules = []
        nc = cursor.copy()
        nc.from_rule = self
        for action in self.actions:
            action_name = action.getName()
            if action_name == 'load':
                tgt_reg = action.load.key.split("_")[2].lower()

                nc.fields[tgt_reg] = action.load.value
                continue
            elif action_name == 'action_type':
                if action.action_type == 'strip_vlan':
                    nc.fields['dl_vlan'] = 0
                elif action.action_type == 'drop':
                    self.annotations['action'] = 'drop'
                    # We could uncomment that to also print out the drops in
                    # the summary.
                    # self._dump.output_nodes['DROP'][self.conditions].add(self)
                    break
                elif action.action_type == 'NORMAL':
                    self._dump.output_nodes['NORMAL'][self.conditions].add(
                        self)
                    break
                continue

            elif action_name == 'output':
                nc.fields['output'] = action.output
                self._dump.output_nodes[action.output][self.conditions].add(
                    self)
                self.annotations['action'] = 'pass'
                # We don't care what happens after, but it could be a resubmit,
                # usually to a drop, in case the port doesn't exist.
                break

            elif action_name == 'resubmit':
                next_table = action.resubmit.resubmit_table
                next_rules = self._dump.tables[next_table]
                # Look ahead
                if len(next_rules) == 1:
                    pass_or_drop = next_rules[0].pass_or_drop()
                    if pass_or_drop:
                        self.annotations['action'] = pass_or_drop
                break

            elif action_name == 'func_call':
                func_params = action.func_call.func_param.asList()
                if action.func_call.func_name == 'ct':
                    if func_params[0][0] != 'commit':
                        for (arg_name, *v) in func_params:
                            if arg_name == 'table':
                                next_rules = self._dump.tables[v[0]]
                    if next_rules:
                        break

            elif action_name == 'conjunction':
                conj = action.conjunction
                # Register self as a potential precursor for conj_id, conj_k
                self._dump.conj_setters[conj.conj_id][conj.conj_k].append(self)
                self._conj_key = (conj.conj_id, conj.conj_k)

        return nc, next_rules, rule_fields_count == 0

    def __repr__(self):
        return "%s\n\t%s" % (self.annotations, self._line)


class FlowDump:
    def __init__(self, br_name: str):
        self.br_name = br_name
        self.flows: List[FlowRule] = []
        self.tables: DefaultDict[int, List[FlowRule]] = (
            collections.defaultdict(list))
        self.priorities: DefaultDict[int, List[FlowRule]] = (
            collections.defaultdict(list))
        self.conjunctions: Dict[int, FlowRule] = dict()
        self.conj_setters = collections.defaultdict(
            lambda: collections.defaultdict(list)
        )
        self.output_nodes = collections.defaultdict(
            lambda: collections.defaultdict(set)
        )

    def sort_rules(self):

        for table in self.tables.values():
            table.sort(key=lambda r: (
                -r.priority, r.fields.conj_id if r.fields.conj_id else 0))

    def from_file(self, path):
        with open(path, 'r') as fd:
            for line in fd.readlines():
                self.parse_flow_line(line.strip())

    def parse_flow_line(self, line):
        fr = FlowRule.from_line(line, self)
        self.tables[fr.table].append(fr)
        self.priorities[fr.priority].append(fr)
        if fr.fields.conj_id:
            self.conjunctions[fr.fields.conj_id] = fr
        self.flows.append(fr)

    def walk_dump(self, initial_cursor: FlowCursor, root_rule: FlowRule=None):
        """
        Walk the dump
        """
        self.sort_rules()
        root_rule = root_rule or self.tables[None][-1]
        call_stack = [(root_rule, initial_cursor)]
        seen = set()
        passed_set = set()
        passed: List[Tuple[FlowRule, FlowCursor]] = list()

        while call_stack:
            candidate_rule, cursor = call_stack.pop(0)
            if (candidate_rule, cursor) in seen:
                continue
            if candidate_rule.fields.conj_id:
                # If we pass through a conj_id rule, collect all the
                # conjunction precursors into the rule's _parent_rules
                # Normally, because the rules are sorted, the conj_id rule
                # should be parsed after all its precursors.
                conj_precursors = self.conj_setters[
                    candidate_rule.fields.conj_id]
                for rules in conj_precursors.values():
                    # Conjunction precursors are grouped, but we don't care
                    # about that when we reverse-walk the graph. So we
                    # flatten all that.
                    candidate_rule._parent_rules.add(tuple(rules))

            next_cursor, next_rules, _ = candidate_rule.passes_cursor(cursor)

            if next_cursor:
                # This rule matches the current cursor
                if candidate_rule not in passed_set:
                    passed.append((candidate_rule, cursor))
                    passed_set.add(candidate_rule)
                cursor = next_cursor
                # This rule passed, so we don't want to process it again
                seen.add((candidate_rule, cursor))
            if next_rules:
                # This rule has next_rules, so for each next_rule, we add
                # the current candidate_rule as a parent, accumulate the
                # conditions and stack the rule onto the call_stack for
                # further exploration.
                for nr in next_rules[::-1]:
                    nr._parent_rules.add((candidate_rule,))
                    nr._accumulated_conditions |= candidate_rule.conditions
                    call_stack.insert(0, (nr, next_cursor))
        return passed

    def rules_conditions_union(self, rules):
        """
        Returns the union (OR) of the conditions of rules.

        We have to go through this alembic'ed function in order to merge
        ranges (for example port ranges) as an high level rule (for example,
        allow port 1 to 31766) are broken down into a multitude of hard to read
        flow rules. Return them in DNF notation, as it looks nicer to read.
        """
        ored, range_accumulator = self.rule_conditions_or(rules)

        for key_name, ranges in range_accumulator.items():
            closed_interval = close_intervals(sm.Union(*ranges))

            ored = ored.replace(
                    sm.Symbol(key_name),
                    closed_interval.as_relational(
                        sm.Symbol(key_name.partition("__range_")[2])
                    ))
        return sm.to_dnf(ored)

    def rule_conditions_or(self, rules):
        """OR rules conditions, extract the various ranges they contain."""
        ored = False
        range_accumulator = collections.defaultdict(list)
        for rule in rules:

            if isinstance(rule.simplified_conditions, sm.And):

                for term in rule.simplified_conditions.args:
                    if not term.is_Symbol:
                        continue

                    if term.name.startswith('__range_'):
                        range_accumulator[term.name].append(
                            rule._ranges[term.name]
                        )
            ored |= rule.simplified_conditions

        return ored, range_accumulator


class VMFlowDumper:

    def get_interfaces_for_vm(self, vm_uuid):
        conn = libvirt.openReadOnly(None)
        dom = conn.lookupByUUIDString(vm_uuid)
        dom_xml = ET.fromstring(dom.XMLDesc())
        interfaces = []
        for interface_xml in dom_xml.findall('./devices/interface'):
            interface = dict(
                mac_address=interface_xml.find('./mac').attrib['address'],
                target_dev=interface_xml.find('./target').attrib['dev'],
            )
            interfaces.append(interface)

        for interface in interfaces:
            vlan_id = subprocess.check_output(
                ("ovs-vsctl get port %s tag" %
                 interface['target_dev']).split(),
                universal_newlines=True
            )
            interface['vlan_id'] = int(vlan_id) if vlan_id != '[]' else None
        return interfaces

    def get_flow_dump(self, bridge_name):
        flows_lines = subprocess.check_output(
            ("ovs-ofctl --names --no-stats "
             "--read-only --color=always --sort "
             "dump-flows %s" % bridge_name).split(),
            universal_newlines=True
        )
        fd = FlowDump(bridge_name)
        for line in flows_lines.split("\n"):
            if line:
                fd.parse_flow_line(line)
        return fd

    def read_flow_dump(self, flow_str):
        fd = FlowDump('from-file')
        for line in flow_str:
            if line:
                fd.parse_flow_line(line)
        return fd

    def make_vm_egress_cursor(self, interface):
        cursor = FlowCursor()
        cursor.fields['in_port'] = interface['target_dev']
        cursor.fields['dl_vlan'] = 0
        cursor.fields['dl_dst'] = 'UNSET'
        return cursor

    def make_vm_ingress_cursor(self, interface):
        cursor = FlowCursor()
        # VM ingress traffic isn't matched by in_port
        cursor.fields['in_port'] = 'IGNORE'
        # VM ingress traffic has a vlan set
        cursor.fields['dl_vlan'] = interface['vlan_id']
        cursor.fields['dl_dst'] = interface['mac_address']
        return cursor

    def make_cursor_from_fields(self, fields):
        cursor = FlowCursor()
        for k, v in fields.items():
            try:
                cursor.fields[k] = int(v)
            except ValueError:
                cursor.fields[k] = v
        return cursor


def parse_args():
    parser = argparse.ArgumentParser(description="Get VM flow rules.")

    data_source = parser.add_mutually_exclusive_group(required=True)
    data_source.add_argument('--vm-uuid', type=str)
    data_source.add_argument('--flow-file', type=argparse.FileType('r'))

    direction = parser.add_mutually_exclusive_group(required=True)
    direction.add_argument('--egress', action='store_const', dest='direction',
                           const='egress')
    direction.add_argument('--ingress', action='store_const', dest='direction',
                           const='ingress')
    direction.add_argument('--field', nargs='+', help='Fields value',
                           type=lambda x: [x.strip() for x in x.split('=')])
    parser.add_argument('--interface', required=False,
                        help="Interface to filter on")

    return parser.parse_args()


class DNFPrinter(sm.printing.StrPrinter):
    def _print_Equality(self, eq):
        return " == ".join(
            self.doprint(arg) for arg in eq.args
        )

    def _print_Or(self, expr):
        out = []
        for arg in expr.args[:-1]:
            out.append(self.doprint(arg) + " | ")
        out.append(self.doprint(expr.args[-1]))

        return "\n".join(out)


def print_rule_tree(rt: Set['FlowRule']):
    """
    Recursively explore rt-contained rules' parents.
    """

    rt = rt.copy()
    res = []
    seen = set()
    while rt:
        rule = rt.pop()
        if rule in seen:
            continue
        seen.add(rule)

        res.insert(0, rule)
        for parent_rule_groups in rule._parent_rules:
            for pr in parent_rule_groups:
                rt.add(pr)
    res.sort(key=human_rule_sorter)
    return res


def dnfprint(expr, **settings):

    p = DNFPrinter(settings)
    return p.doprint(expr)


if __name__ == "__main__":
    args = parse_args()
    vmfd = VMFlowDumper()

    cursors_to_run = []

    if args.vm_uuid:
        fd = vmfd.get_flow_dump('br-int')
        interfaces = vmfd.get_interfaces_for_vm(args.vm_uuid)
        print(interfaces)
        if args.interface:
            interfaces = [i for i in interfaces
                          if i['target_dev'] == args.interface]
        for interface in interfaces:
            if args.direction == "ingress":
                cursor = vmfd.make_vm_ingress_cursor(interface)
            elif args.direction == "egress":
                cursor = vmfd.make_vm_egress_cursor(interface)
            cursors_to_run.append(cursor)

    else:
        fd = vmfd.read_flow_dump(args.flow_file.readlines())
        cursor = vmfd.make_cursor_from_fields(dict(args.field))
        cursors_to_run.append(cursor)

    for cursor in cursors_to_run:
        print("# Walking flow dump with cursor %s" % cursor)
        print("# Applicable rules : ")
        rules = fd.walk_dump(cursor)
        rules.sort(key=lambda r: human_rule_sorter(r[0]))
        for rule in rules:
            print(rule[0]._line.strip())

        print("\n\n\n# Outputs Summary",
              "# This summary can help you see at a glance what paths could",
              "# be followed by the traffic leading to a successful output.",
              "# When possible, the rules are annotated with higher level",
              "# information.",
              "# The summary is not very precise, only works with rules that",
              "# have an active output action and doesn't necessarily",
              "# handle all the rule conditions.", sep="\n")
        for output, output_nodes in fd.output_nodes.items():
            # For each output node, we OR all the direct parents and
            # "humanize" any ranges inthere
            for condition_root, to_merge in output_nodes.items():
                merged = fd.rules_conditions_union(to_merge)

                if merged is not True:
                    # Summarize the rules group
                    print("Following output path can be grouped as :",
                          "output to", output, "if : ")
                    print("\n".join("  " + l for l
                                    in dnfprint(merged).split("\n")))
                else:
                    print("Output path :")
                for rule in print_rule_tree(to_merge):
                    print("    " + rule._line.strip())
