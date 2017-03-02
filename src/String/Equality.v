Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Require Import Hapsl.Ascii.Equality.
Require Import Hapsl.String.Transform.

Import AsciiEqualityNotations.

(* Returns true if two strings are equivalent, otherwise returns false. *)
Fixpoint beq_string (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1', String c2 s2' => andb (c1 ==_a c2) (beq_string s1' s2')
  | _, _ => false
  end.

(* Proves the reflexivity of boolean string equality. *)
Lemma beq_string_reflexive : forall (s : string),
  Is_true (beq_string s s).
Proof.
  intros.
  induction s as [| h tail IH].
  + reflexivity.
  + unfold beq_string.
    unfold "==_a".
    rewrite -> compare_ascii_reflexive.
    auto.
Qed.

(* Returns true if two strings are equivalent, disregarding case, otherwise 
   returns false. *)
Definition beq_string_ignorecase (s1 s2 : string) : bool :=
  beq_string (string_to_lower s1) (string_to_lower s2).

(* Equality notations module for ASCII strings. *)
Module StringEqualityNotations.

  (* String equality operator. *)
  Notation "a ==_s b" := (beq_string a b) (at level 30).

End StringEqualityNotations.
