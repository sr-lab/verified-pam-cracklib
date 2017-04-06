#!/bin/bash

# Removes line breaks from the given string.
function removeLineBreaks
{
	RESULT=$1
	RESULT="${RESULT//[$'\n']}"
        RESULT="${RESULT//[$'\r']}"
	echo $RESULT
}

COMMA="" # Initially, no separator.

printf "{\"started\":\"%s\",\"runs\":[" $(date +%s%N) # Start JSON structure.

# For each line in password file.
while IFS='' read -r line || [[ -n "$line" ]]; do

	# Remove stray line breaks in password.
	line=$(removeLineBreaks "$line")

	# Extract result of attempted password change.
	RESULT=$(expect -f passwd.exp "$USER" "$line")
	RESULT="${RESULT//New password: /}"
	RESULT="${RESULT//Retype new password: /}"
	RESULT="${RESULT/spawn passwd $USER/}"
	RESULT="${RESULT/./. }" # Space out sentences.
	RESULT=$(removeLineBreaks "$RESULT")

	# Time in nanoseconds.
	TIME=$(date +%s%N)

	# Check if password is valid.
	VALID="true"
	if [[ $RESULT =  *"BAD PASSWORD"* ]]; then
		VALID="false"
	fi

	# Print object.
	CLEANLINE="${line//\\/\\\\}"
	printf "%s{\"password\":\"%s\",\"time\":\"%s\",\"result\":\"%s\",\"valid\":%s}" "$COMMA" "$CLEANLINE" "$TIME" "$RESULT" "$VALID"

	# Now we need a separator.
	COMMA=","

done < "$1"

echo "]}" # End JSON structure.

