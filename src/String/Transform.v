Require Import Coq.Bool.Bool.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Hapsl.Ascii.Class.
Require Import Hapsl.String.Equality.

Import StringEqualityNotations.

(* Notations for string transformation. *)
Module StringTransformationNotations.

  (* Notation for appending a string to another. *)
  Notation "a +=_s b" := (append a b) (at level 60, right associativity).

End StringTransformationNotations.

Import StringTransformationNotations.

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

(* Returns a string, reversed. *)
Fixpoint string_reverse (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (string_reverse s') +=_s (String c EmptyString)
  end.

(* Prove that appending an empty stirng to a string is reflexive. *)
Theorem append_empty_reflexive : forall (s : string),
  s +=_s EmptyString = s.
Proof.
  intros.
  induction s.
  + reflexivity.
  + simpl.
    rewrite -> IHs.
    reflexivity.
Qed.

(* Prove that appending one string to another is an associative operation. *)
Theorem append_associative : forall (l m n : string),
  l +=_s m +=_s n = (l +=_s m) +=_s n.
Proof.
  (* TODO: Odd semicolon behavior. Splitting these up doesn't work. *)
  intros l m n; induction l; simpl; f_equal; auto.
Qed.

(* Prove that string reverse/append is distributive. *)
Theorem string_reverse_append_distributive : forall (x y : string),
  string_reverse (x +=_s y) = string_reverse y +=_s string_reverse x.
Proof.
  induction x as [| a l IHl].
  + destruct y.
    - simpl. reflexivity.
    - simpl.
      rewrite append_empty_reflexive.
      reflexivity.
  + intros.
    simpl.
    rewrite -> IHl.
    rewrite <- append_associative.
    reflexivity.
Qed.

(*Lemma string_reverse_unit : forall (s : string) (c : ascii),
  string_reverse (String c s) = (string_reverse s) +=_s (String c EmptyString).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma string_reverse_involutive : forall (l : string),
  string_reverse (string_reverse l) = l.
Proof.
  induction l as [| a l IHl].
  + simpl; auto.
  + rewrite (string_reverse_unit (string_reverse l) a).
rewrite IHl; auto.
Qed.*)