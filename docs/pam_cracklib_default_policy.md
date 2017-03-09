# Default Policy 
Passwords must:

* Have a Levenshtein distance of 5 or greater from the previous password, if any
* Be at least 9 characters long, however:
    + Passwords may be 1 character shorter if they contain lower case letters
    + Passwords may be 1 character shorter if they contain upper case letters
    + Passwords may be 1 character shorter if they contain digit characters
    + Passwords may be 1 character shorter if they contain other characters
    + This shortening of max length will stack, making for a minimum length of 
      `9 - 4 = 5` for passwords containing all 4 classes.