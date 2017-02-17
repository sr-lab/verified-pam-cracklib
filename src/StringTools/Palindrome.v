Require Import Coq.Strings.String.

Require Import Pam.StringExtensions.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition Palindrome (s : string) : bool :=
  string_eqb s (string_reverse s).

