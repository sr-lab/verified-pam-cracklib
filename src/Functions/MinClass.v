Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Pam.AsciiExtensions.
Require Import Pam.BoolExtensions.
Require Import Pam.StringExtensions.

(* Converts a string to lower case. *)
Fixpoint string_to_lower (s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_lower c) (string_to_lower s)
  end.

(* Converts a string to upper case. *)
Fixpoint string_to_upper (s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_upper c) (string_to_upper s)
  end.

(* Returns true if two strings are equivalent, disregarding case, otherwise 
   returns false. *)
Fixpoint string_eq_ignorecase (s1 s2 : string) : bool :=
  string_eqb (string_to_lower s1) (string_to_lower s2).

(* Counts the number of characters in a string that satisfy a function. *)
Fixpoint string_count (s : string) (f : ascii->bool) : nat :=
  match s with
  | EmptyString => 0
  | String c s => (bool_to_nat (f c)) + (string_count s f)
  end.

(* Returns the number of lower case letters in a string. *)
Fixpoint string_count_lower (s : string) : nat :=
  string_count s is_lower.

(* Returns the number of upper case letters in a string. *)
Fixpoint string_count_upper (s : string) : nat :=
  string_count s is_upper.

(* Returns the number of digits in a string. *)
Fixpoint string_count_digit (s : string) : nat :=
  string_count s is_digit.

(* Returns the number of other characters in a string (that is, not upper case 
   letter, lower case letter or digit). *)
Fixpoint string_count_other (s : string) : nat :=
  string_count s is_other.

(* Returns true if any of the characters in a string satisfy a function, 
   otherwise returns false. *)
Fixpoint string_contains (s : string) (f : string->nat) : bool :=
  ltb 0 (f s).

(* Returns true if any of the characters in a string are lower case letters,
   otherwise returns false. *)
Fixpoint string_contains_lower (s : string) : bool :=
  string_contains s string_count_lower.

(* Returns true if any of the characters in a string are upper case letters,
   otherwise returns false. *)
Fixpoint string_contains_upper (s : string) : bool :=
  string_contains s string_count_upper.

(* Returns true if any of the characters in a string are digits, otherwise 
   returns false. *)
Fixpoint string_contains_digit (s : string) : bool :=
  string_contains s string_count_digit.

(* Returns true if any of the characters in a string are neither lower case 
   letters, upper case letters or digits. Otherwise returns false. *)
Fixpoint string_contains_other (s : string) : bool :=
  string_contains s string_count_other.

(* Returns a number from 0-4 representing the number of character classes in a 
   string (lower case letters, upper case letters, digits and others). *)
Fixpoint string_count_character_classes (s : string) : nat :=
  (bool_to_nat (string_contains_lower s)) 
    + (bool_to_nat (string_contains_upper s)) 
    + (bool_to_nat (string_contains_digit s))
    + (bool_to_nat (string_contains_other s)).

(* Returns true if the number of character classes in a string is greater than
   or equal to the given minimum. Otherwise returns false. *)
Fixpoint minclassb (s : string) (m : nat) : bool :=
  negb (ltb (string_count_character_classes s) m).
  
(* Returns 1 if the number of character classes in a string is greater than
   or equal to the given minimum. Otherwise returns 0. *)
Fixpoint minclass (s : string) (m : nat) : nat :=
  bool_to_nat (minclassb s m).
  