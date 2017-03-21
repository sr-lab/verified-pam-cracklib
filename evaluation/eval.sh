#!/bin/bash

while IFS='' read -r line || [[ -n "$line" ]]; do
    LN=$(printf '%s' "$line")
    RS=$(echo $LN | passwd)
    echo $LN
    printf "%s, %s" $LN $RN
done < "$1"

