Require Import Coq.Strings.String.
Require Import Pam.StringExtensions.

Definition Palindrome (s : string) : bool :=
  string_eqb s (string_reverse s).

