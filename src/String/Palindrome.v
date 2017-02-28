Require Import Coq.Strings.String.

Require Import Hapsl.String.Equality.
Require Import Hapsl.String.Transform.

Import StringEqualityNotations.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition palindrome (s : string) : bool :=
  s ==_s (string_reverse s).
