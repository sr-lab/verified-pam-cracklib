# Options
The official documentation for each option is contained below. Useful for
intention extraction

## Option `debug`

This option makes the module write information to syslog3 indicating the 
behavior of the module (this option does not write password information to the 
log file).


## Option `authtok_type=XXX`

The default action is for the module to use the following prompts when 
requesting passwords: "New UNIX password: " and "Retype UNIX password: ". The 
example word UNIX can be replaced with this option, by default it is empty.


## Option `retry=N`

Prompt user at most N times before returning with error. The default is 1.


## Option `difok=N`

This argument will change the default of 5 for the number of character changes 
in the new password that differentiate it from the old password.


## Option `minlen=N`

The minimum acceptable size for the new password (plus one if credits are not 
disabled which is the default). In addition to the number of characters in the 
new password, credit (of +1 in length) is given for each different kind of 
character (other, upper, lower and digit). The default for this parameter is 9 
which is good for a old style UNIX password all of the same type of character 
but may be too low to exploit the added security of a md5 system.  Note that 
there is a pair of length limits in Cracklib itself, a "way too short" limit of 
4 which is hard coded in and a defined limit (6) that will be checked without 
reference to minlen. If you want to allow passwords as short as 5 characters you
should not use this module.


## Option `dcredit=N`

(N &gt;= 0) This is the maximum credit for having digits in the new password. If 
you have less than or N digits, each digit will count +1 towards meeting the 
current minlen value. The default for dcredit is 1 which is the recommended
value for minlen less than 10.

(N &lt; 0) This is the minimum number of digits that must be met for a new 
password.


## Option `ucredit=N`

(N &gt;= 0) This is the maximum credit for having upper case letters in the new
password.  If you have less than or N upper case letters each letter will count 
+1 towards meeting the current minlen value. The default for ucredit is 1 which
is the recommended value for minlen less than 10.

(N &lt; 0) This is the minimum number of upper case letters that must be met for 
a new password.


## Option `lcredit=N`

(N &gt;= 0) This is the maximum credit for having lower case letters in the new 
password. If you have less than or N lower case letters, each letter will count 
+1 towards meeting the current minlen value. The default for lcredit is 1 which 
is the recommended value for minlen less than 10.

(N &lt; 0) This is the minimum number of lower case letters that must be met for a
new password.


## Option `ocredit=N`

(N &gt;= 0) This is the maximum credit for having other characters in the new 
password. If you have less than or N other characters, each character will count 
+1 towards meeting the current minlen value. The default for ocredit is 1 which 
is the recommended value for minlen less than 10.

(N &lt; 0) This is the minimum number of other characters that must be met for a
new password.


## Option `minclass=N`

The minimum number of required classes of characters for the new password. The 
default number is zero. The four classes are digits, upper and lower letters and 
other characters. The difference to the credit check is that a specific class if 
of characters is not required. Instead N out of four of the classes are 
required.


## Option `maxrepeat=N`

Reject passwords which contain more than N same consecutive characters. The 
default is 0 which means that this check is disabled.


## Option `maxsequence=N`

Reject passwords which contain monotonic character sequences longer than N. The 
default is 0 which means that this check is disabled. Examples of such sequence 
are '12345' or 'fedcb'. Note that most such passwords will not pass the 
simplicity check unless the sequence is only a minor part of the password.


## Option `maxclassrepeat=N`

Reject passwords which contain more than N consecutive characters of the same 
class. The default is 0 which means that this check is disabled.


## Option `reject_username`

Check whether the name of the user in straight or reversed form is contained in 
the new password. If it is found the new password is rejected.


## Option `gecoscheck`

Check whether the words from the GECOS field (usualy full name of the user) 
longer than 3 characters in straight or reversed form are contained in the new 
password. If any such word is found the new password is rejected.


## Option `enforce_for_root`

The module will return error on failed check also if the user changing the 
password is root. This option is off by default which means that just the 
message about the failed check is printed but root can change the password 
anyway. Note that root is not asked for an old password so the checks that 
compare the old and new password are not performed.


## Option `use_authtok`

This argument is used to force the module to not prompt the user for a new 
password but use the one provided by the previously stacked password module.


## Option `dictpath=/path/to/dict`

Path to the cracklib dictionaries.
