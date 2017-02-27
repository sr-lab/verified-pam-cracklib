Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Pamba.Ascii.Class.
Require Import Pamba.Bool.Bool.
Require Import Pamba.String.Equality.

Import StringEqualityNotations.

(* Returns true if a string contains a substring, otherwise returns false. *)
Fixpoint contains (h n : string) : bool :=
  match h with 
  | String c s => 
      if length h <? length n then
        false
      else if (substring 0 (length n) h) ==_s n then
        true
      else
        contains s n
  | EmptyString => eqb (length n) 0
  end.

(* Counts the number of characters in a string that satisfy a function. *)
Fixpoint string_count (s : string) (f : ascii->bool) : nat :=
  match s with
  | EmptyString => 0
  | String c s => (nat_of_bool (f c)) + (string_count s f)
  end.

(* Returns the number of lower case letters in a string. *)
Definition string_count_lower (s : string) : nat :=
  string_count s is_lower.

(* Returns the number of upper case letters in a string. *)
Definition string_count_upper (s : string) : nat :=
  string_count s is_upper.

(* Returns the number of digits in a string. *)
Definition string_count_digit (s : string) : nat :=
  string_count s is_digit.

(* Returns the number of other characters in a string (that is, not upper case 
   letter, lower case letter or digit). *)
Definition string_count_other (s : string) : nat :=
  string_count s is_other.

(* Returns true if any of the characters in a string satisfy a function, 
   otherwise returns false. *)
Fixpoint string_contains (s : string) (f : string->nat) : bool :=
  ltb 0 (f s).

(* Returns true if any of the characters in a string are lower case letters,
   otherwise returns false. *)
Definition string_contains_lower (s : string) : bool :=
  string_contains s string_count_lower.

(* Returns true if any of the characters in a string are upper case letters,
   otherwise returns false. *)
Definition string_contains_upper (s : string) : bool :=
  string_contains s string_count_upper.

(* Returns true if any of the characters in a string are digits, otherwise 
   returns false. *)
Definition string_contains_digit (s : string) : bool :=
  string_contains s string_count_digit.

(* Returns true if any of the characters in a string are neither lower case 
   letters, upper case letters or digits. Otherwise returns false. *)
Definition string_contains_other (s : string) : bool :=
  string_contains s string_count_other.

(* Returns a number from 0-4 representing the number of character classes in a 
   string (lower case letters, upper case letters, digits and others). *)
Definition string_count_character_classes (s : string) : nat :=
  (nat_of_bool (string_contains_lower s)) 
    + (nat_of_bool (string_contains_upper s)) 
    + (nat_of_bool (string_contains_digit s))
    + (nat_of_bool (string_contains_other s)).
