#!/bin/bash

COMMA="" # Initially, no separator.

echo "[" # Start JSON array.

# For each line in password file.
while IFS='' read -r line || [[ -n "$line" ]]; do

	# Time in nanoseconds.
	TIME=$(date +%s%N)

	# Result of attempted password change.
	RESULT=$(expect -f passwd.exp "$USER" "$line")
	RESULT="${RESULT//New password: /}"
	RESULT="${RESULT//Retype new password: /}"
	RESULT="${RESULT/spawn passwd $USER/}"
	RESULT=$(echo "${RESULT//[$'\r\n']}")

	# Check if password is valid.
	VALID="true"
	if [[ $RESULT =  *"BAD PASSWORD"* ]]; then
		VALID="false"
	fi

	# Print object.
	printf "%s{\"password\":\"%s\",\"time\":\"%s\",\"result\":\"%s\",\"valid\":%s}" "$COMMA" "$line" "$TIME" "$RESULT" "$VALID"

	# Now we need a separator.
	COMMA=","

done < "$1"

echo "]" # End JSON array.
