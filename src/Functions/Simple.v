Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.

Require Import Pam.AsciiExtensions.
Require Import Pam.Functions.Sequence.

Definition simple (s : string) (m : nat) : bool :=
  ltb (sequence_of s is_same_class 0) m.

