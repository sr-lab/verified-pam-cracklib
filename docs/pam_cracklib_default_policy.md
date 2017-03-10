# Default Policy 
Passwords must:

* Not be identical to the previous password, if any.
* Not be palindromic.
* Not be a rotated version of the old password.
* Not contain case changes only in relation to the previous password, if any.
* Have a Levenshtein distance of 5 or greater from the previous password, if 
  any. [1]
* Be at least 9 characters long [2], however:
    + Passwords may be 1 character shorter if they contain at least 1 lower case
      letter. [3]
    + Passwords may be 1 character shorter if they contain at least 1 upper case 
      letter. [4]
    + Passwords may be 1 character shorter if they contain at least 1 digit 
      character. [5]
    + Passwords may be 1 character shorter if they contain at least 1 other 
      character. [6]
    + This shortening of minimum length will stack, making for a minimum length 
      of `9 - 4 = 5` for passwords containing all 4 classes.
    + Effective minimum length is, then `M = m - c` where `M` is the effective 
      minimum length, `m` is the configured minimum length and c is the number
      of character classes present in the string.
      
The options below map to the assertions above:

* [1] - `difok=5`
* [2] - `minlen=9`
* [3] - `lcredit=1`
* [4] - `ucredit=1`
* [5] - `dcredit=1`
* [6] - `ocredit=1`

The behaviour of `pam_pwquality` is identical to the above by default [as evidenced by the code](https://github.com/cgwalters/libpwquality-git/blob/f835a65d939889e3b36adb9672312dfc7d711c77/src/pwqprivate.h#L36-L41).
