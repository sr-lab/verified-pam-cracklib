#!/bin/bash

COMMA=""
echo "["
while IFS='' read -r line || [[ -n "$line" ]]; do
	TIME=$(date +%s%N)
	RESULT=$(expect -f passwd.exp "$USER" "$line")
	#echo $RESULT
	printf "%s{\"password\":\"%s\",\"time\":\"%s\",\"result\":\"%s\"}" "$COMMA" "$line" "$TIME" "$RESULT"
	COMMA=","
done < "$1"
echo "]"
