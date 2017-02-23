Require Import Coq.Strings.String.

Require Import Pam.StringExtensions.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition palindrome (s : string) : bool :=
  string_eqb s (string_reverse s).
  