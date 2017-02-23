Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Pam.BoolExtensions.
Require Import Pam.StringExtensions.

(* Returns true if a string contains a substring, otherwise returns false. *)
Fixpoint contains (h n : string) : bool :=
  match h with 
  | String c s => 
      if length h <? length n then
        false
      else if string_eqb (substring 0 (length n) h) n then
        true
      else
        contains s n
  | EmptyString => eqb (length n) 0
  end.

(* Returns true if a string contains a substring or a reversed version of that 
   substring, otherwise returns false. *)
Fixpoint wordcheck (h n : string) : bool :=
  orb (contains h n) (contains (string_reverse h) n).
