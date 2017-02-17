Require Import Coq.Strings.String.

Require Import Pam.BoolExtensions.
Require Import Pam.StringExtensions.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition palindromeb (s : string) : bool :=
  string_eqb s (string_reverse s).

(* Returns 1 if a string is a palindrome, otherwise returns 0. *)
Definition palindrome (s : string) : nat :=
  bool_to_nat (palindromeb s).