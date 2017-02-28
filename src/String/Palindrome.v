Require Import Coq.Strings.String.

Require Import Pamba.String.Equality.
Require Import Pamba.String.Transform.

Import StringEqualityNotations.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition palindrome (s : string) : bool :=
  s ==_s (string_reverse s).
