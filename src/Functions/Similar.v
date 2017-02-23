Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.

Require Import Pam.Functions.Levenshtein.

Definition similar (a b : string) (d : nat) : bool :=
  negb (ltb (levenshtein_distance a b) d).
  