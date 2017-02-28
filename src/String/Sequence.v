Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Hapsl.Bool.Bool.
Require Import Hapsl.Ascii.Equality.

(* Returns true if one character is exactly one more than another, otherwise 
   returns false. *)
Definition consecutive_up (c1 c2 : ascii) : bool :=
  eqb (nat_of_ascii c1) ((nat_of_ascii c2) - 1).

(* Returns true if one character is exactly one less than another, otherwise 
   returns false. *)
Definition consecutive_down (c1 c2 : ascii) : bool :=
  eqb (nat_of_ascii c1) ((nat_of_ascii c2) + 1).

(* Returns the maximum number of times consecutive characters in a string 
   satisfy a function. *)
Fixpoint sequence_of (s : string) (f : ascii->ascii->bool) (a : nat) : nat :=
  match s with
  | EmptyString => a
  | String c1 s1 => 
    match s1 with
    | EmptyString => a
    | String c2 s2 => 
      if f c1 c2 then
        sequence_of s1 f (a + 1)
      else
        max a (sequence_of s1 f 0)
    end
  end.

(* Returns the maximum number of times consecutive characters in a string are 
   one more than their predecessor. *)
Definition sequence_up (s : string) : nat :=
  sequence_of s consecutive_up 0.

(* Returns the maximum number of times consecutive characters in a string are 
   one less than their predecessor. *)
Definition sequence_down (s : string) : nat :=
  sequence_of s consecutive_down 0.

(* Returns the maximum number of times consecutive characters in a string are 
   the same as their predecessor. *)
Definition sequence_eq (s : string) : nat :=
  sequence_of s beq_ascii 0.
