# Copyright (c) 2019 VEXXHOST, Inc.
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

"""
Clean up Heat stacks

This script grabs a list of all stacks in DELETE_FAILED state and tries to
delete them again.  For usage, please run the script with `--help`.
"""

import argparse

import openstack

options = argparse.ArgumentParser(description='OpenStack Heat Clean-up')
cloud = openstack.connect(options=options)

def cleanup_stack(stack):
    # Skip anything that isn't DELETE_FAILED
    if stack.status != 'DELETE_FAILED':
        return

    # Get a list of all the resources of the stack
    resources = list(cloud.orchestration.resources(stack))

    # If we don't have any resources, we can consider this stack gone.
    if len(resources) == 0:
        print('[{}] no resources, deleting stack'.format(stack.id))
        cloud.orchestration.delete_stack(stack)
        return

    # Find resources that are DELETE_FAILED
    for resource in resources:
        # Skip resources that are not DELETE_FAILED
        if resource.status != 'DELETE_FAILED':
            continue

        # Clean up and nested stacks
        if resource.resource_type in ('OS::Heat::ResourceGroup'):
            stack_id = resource.physical_resource_id
            nested_stack = cloud.orchestration.find_stack(stack_id)
            cleanup_stack(nested_stack)
            continue

        # This is protection to make sure that we only delete once we're sure
        # that all resources are gone.
        print(stack, resource)
        raise

    # At this point, the stack should be ready to be deleted
    print("[{}] deleting..".format(stack.id))
    cloud.orchestration.delete_stack(stack)


for stack in cloud.orchestration.stacks():
    cleanup_stack(stack)