# Default Policy 
Passwords must:

* Have a Levenshtein distance of 5 or greater from the previous password, if any
  [1]
* Be at least 9 characters long, however:
    + Passwords may be 1 character shorter if they contain at least 1 lower case
      letter. [2]
    + Passwords may be 1 character shorter if they contain at least 1 upper case 
      letter. [3]
    + Passwords may be 1 character shorter if they contain at least 1 digit 
      character. [4]
    + Passwords may be 1 character shorter if they contain at least 1 other 
      character. [5]
    + This shortening of max length will stack, making for a minimum length of 
      `9 - 4 = 5` for passwords containing all 4 classes.
      
[1] - `difok=5`
[2] - `lcredit=1`
[3] - `ucredit=1`
[4] - `dcredit=1`
[5] - `ocredit=1`
