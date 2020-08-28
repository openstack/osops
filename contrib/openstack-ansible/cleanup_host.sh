#!/bin/bash

# This script reclaims space on a host that might
# be low on disk space by getting rid of logs and
# extra data.

find /openstack/log/ -type f | xargs -n1 truncate -s0
