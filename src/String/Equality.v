Require Import Coq.Strings.String.

Require Import Pamba.Ascii.Equality.
Require Import Pamba.String.Transform.

Import AsciiEqualityNotations.

(* Returns true if two strings are equivalent, otherwise returns false. *)
Fixpoint beq_string (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1', String c2 s2' => andb (c1 ==_a c2) (beq_string s1' s2')
  | _, _ => false
  end.

(* Returns true if two strings are equivalent, disregarding case, otherwise 
   returns false. *)
Definition beq_string_ignorecase (s1 s2 : string) : bool :=
  beq_string (string_to_lower s1) (string_to_lower s2).

(* Equality notations module for ASCII strings. *)
Module StringEqualityNotations.

  (* String equality operator. *)
  Notation "a ==_s b" := (beq_string a b) (at level 30).

End StringEqualityNotations.
