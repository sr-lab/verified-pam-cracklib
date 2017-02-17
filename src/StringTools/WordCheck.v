Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

(* Returns true if two strings are equivalent, otherwise returns false. *)
Fixpoint string_eq(s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1', String c2 s2' => andb
    (beq_nat (nat_of_ascii c1) (nat_of_ascii c2)) (string_eq s1' s2')
  | _, _ => false
  end.

(* Returns true if a string contains a substring, otherwise returns false. *)
Fixpoint contains(h n: string) : bool :=
  match h with 
  | String c s => 
      if length h <? length n then
        false
      else if string_eq (substring 0 (length n) h) n then
        true
      else
        contains s n
  | EmptyString => eqb (length n) 0
  end.

(* Returns a string, reversed. *)
Fixpoint str_reverse(s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => append (str_reverse s') (String c EmptyString)
  end.

(* Returns true if a string contains a substring or a reversed version of that 
   substring, otherwise returns false. *)
Fixpoint wordcheck(s w : string) : bool :=
  orb (contains s w) (contains (str_reverse s) w).
