#!/bin/bash

while IFS='' read -r line || [[ -n "$line" ]]; do
    LN=$(printf '%s' "$line")
    RS=$(echo $LN | passwd)
    NT=$(date +%s%N)
    printf "%s, %s, %s" $LN $RN $NT
done < "$1"

