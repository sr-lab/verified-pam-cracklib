#!/bin/bash

while IFS='' read -r line || [[ -n "$line" ]]; do
	printf "%s\n>>>\n" $line
	expect -f passwd.exp $USER $line
	printf "\n<<<\n"
done < "$1"

