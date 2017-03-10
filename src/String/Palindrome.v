Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Require Import Hapsl.String.Equality.
Require Import Hapsl.String.Transform.

Import StringEqualityNotations.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition palindrome (s : string) : bool :=
  s ==_s (string_reverse s).

(* Prove that palindrome behaves correctly. *)
Theorem palindrome_correct : forall (s : string),
  s = string_reverse s -> Is_true (palindrome s).
Proof.
  intros.
  unfold palindrome.
  rewrite <- H.
  rewrite -> beq_string_reflexive.
  reflexivity.
Qed.
