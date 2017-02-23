Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Pam.BoolExtensions.

(* Returns true if one character is exactly one more than another, otherwise 
   returns false. *)
Definition consec_up (c1 c2 : ascii) : bool :=
  eqb (nat_of_ascii c1) ((nat_of_ascii c2) - 1).

(* Returns true if one character is exactly one less than another, otherwise 
   returns false. *)
Definition consec_down (c1 c2 : ascii) : bool :=
  eqb (nat_of_ascii c1) ((nat_of_ascii c2) + 1).

(* Returns true if one character is exactly equal to another, otherwise 
   returns false. *)
Definition consec_eq (c1 c2 : ascii) : bool :=
  eqb (nat_of_ascii c1) (nat_of_ascii c2).

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
Fixpoint sequence_up (s : string) : nat :=
  sequence_of s consec_up 0.

(* Returns the maximum number of times consecutive characters in a string are 
   one less than their predecessor. *)
Fixpoint sequence_down (s : string) : nat :=
  sequence_of s consec_down 0.

(* Returns the maximum number of times consecutive characters in a string are 
   the same as their predecessor. *)
Fixpoint sequence_eq (s : string) : nat :=
  sequence_of s consec_eq 0.

(* Returns true if a given string contains consecutive character sequences 
   longer than the specified maximum length, otherwise returns false. *)
Fixpoint sequence (s : string) (m : nat) : bool :=
  leb m (max (sequence_up s) (sequence_down s)).

(* Returns true if a given string contains consecutive idential characters
   longer than the specified maximum length, otherwise returns false. *)
Fixpoint consecutive (s : string) (m : nat) : bool :=
  leb m (sequence_eq s).
