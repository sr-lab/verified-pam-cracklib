Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

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
