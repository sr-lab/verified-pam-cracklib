Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Pam.AsciiExtensions.

(* Converts a string to lower case. *)
Fixpoint string_to_lower (s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_lower c) (string_to_lower s)
  end.

(* Converts a string to upper case. *)
Fixpoint string_to_upper (s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_upper c) (string_to_upper s)
  end.

(* Returns true if two strings are equivalent, otherwise returns false. *)
Fixpoint string_eqb (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1', String c2 s2' => andb
    (beq_nat (nat_of_ascii c1) (nat_of_ascii c2)) (string_eqb s1' s2')
  | _, _ => false
  end.

(* Returns true if two strings are equivalent, disregarding case, otherwise 
   returns false. *)
Fixpoint string_eq_ignorecase (s1 s2 : string) : bool :=
  string_eqb (string_to_lower s1) (string_to_lower s2).

(* Returns true if two strings are not equivalent, otherwise returns false. *)
Fixpoint string_neqb (s1 s2 : string) : bool :=
  negb (string_eqb s1 s2).

(* Returns a string, reversed. *)
Fixpoint string_reverse (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => append (string_reverse s') (String c EmptyString)
  end.

