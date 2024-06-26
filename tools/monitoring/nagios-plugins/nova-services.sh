#!/bin/bash

source ~/openrc

output=$(nova service-list | tail -n +3 | grep down)
if [ $? -eq 0 ]; then
    echo -n "CRITICAL - OpenStack Nova services down: "
    echo "${output}" | awk '{print $2,$4}' | while read LINE; do
        echo -n "${LINE}; "
    done
    echo ""
    exit 2
else
    echo "OK - All nodes up"
    exit 0
fi
