#!/bin/bash

# Removes line breaks from the given string.
function removeLineBreaks
{
	RESULT=$1
	RESULT="${RESULT//[$'\n']}"
	RESULT="${RESULT//[$'\r']}"
	echo $RESULT
}

printf "started: %s"
printf "password, time, result, valid"

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
	printf "%s, %s, %s, %s" "$CLEANLINE" "$TIME" "$RESULT" "$VALID"

done < "$1"
