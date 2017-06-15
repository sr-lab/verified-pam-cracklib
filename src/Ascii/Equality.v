Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.

Require Import Hapsl.CpdtTactics.

(* Returns the comparison of two ASCII characters. *)
Definition compare_ascii (a b : ascii) : comparison  :=
  N.compare (N_of_ascii a) (N_of_ascii b).

(* Prove that the compare_ascii function implies the equality of two ASCII 
 * characters. *)
Theorem compare_ascii_implies_equality : forall (a b : ascii),
  (compare_ascii a b) = Eq -> a = b.
Proof.
  intros.
  rewrite <- ascii_N_embedding with (a := a).
  rewrite <- ascii_N_embedding with (a := b).
  f_equal.
  now apply N.compare_eq_iff.
Qed.

(* Prove that comparing an ASCII character to itself gives Eq. *)
Lemma compare_ascii_reflexive : forall (a : ascii),
  compare_ascii a a = Eq.
Proof.
  intro x.
  unfold compare_ascii.
  now apply N.compare_eq_iff.
Qed.

(** Prove that compare_ascii is symmetric when the result is Eq. *)
Lemma compare_ascii_eq_symmetric : forall (a b : ascii),
    compare_ascii a b = Eq -> compare_ascii b a = Eq.
Proof.
  intros.
  rewrite compare_ascii_implies_equality with (a := a) (b := b).
  + rewrite compare_ascii_reflexive.
    reflexivity.
  + rewrite H.
    reflexivity.
Qed.

(** Prove that compare_ascii is asymmetric when the result is not Eq. **)
Lemma compare_ascii_lt_gt_asymmetric : forall (a b : ascii),
    (compare_ascii a b) = Lt <-> (compare_ascii b a) = Gt.
Proof.
  split.
  + unfold compare_ascii.
    intros.
    apply N.compare_gt_iff in H.
    rewrite H.
    reflexivity.
  + unfold compare_ascii.
    intros.
    apply N.compare_gt_iff in H.
    rewrite H.
    reflexivity.
Qed.

(** Prove that compare_ascii is transitive when the result is Eq. *)
Lemma compare_ascii_eq_transitive : forall (a b c : ascii),
    compare_ascii a b = Eq /\ compare_ascii b c = Eq -> compare_ascii a c = Eq.
Proof.
  intros.
  rewrite compare_ascii_implies_equality with (a := a) (b := b). (* Intuition? *)
  + decompose [and] H.
    rewrite H1.
    reflexivity.
  + decompose [and] H.
    rewrite H0.
    reflexivity.
Qed.

(* Boolean equality for ASCII characters. *)
Definition beq_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Eq => true
    | _ => false
  end.

(* Prove boolean equality for ASCII characters is reflexive. *)
Lemma beq_ascii_reflexive : forall (a : ascii),
  beq_ascii a a = true.
Proof.
  intros.
  unfold beq_ascii.
  rewrite -> compare_ascii_reflexive.
  reflexivity.
Qed.

(* Prove that beq_ascii is symmetric. *)
Theorem beq_ascii_symmetric : forall (a b : ascii),
    beq_ascii a b = beq_ascii b a.
Proof.
  intros.
  unfold beq_ascii.
  case_eq (compare_ascii a b).
  + intros.
    apply compare_ascii_eq_symmetric in H.
    rewrite H.
    reflexivity.
  + intros.
    apply compare_ascii_lt_gt_asymmetric in H.
    rewrite H.
    reflexivity.
  + intros.
    apply compare_ascii_lt_gt_asymmetric in H.
    rewrite H.
    reflexivity.
Qed.

(** Prove that (beq_ascii a b) is true if and only if a = b. *)
Lemma beq_ascii_iff_equality : forall (a b : ascii),
    beq_ascii a b = true <-> a = b.
Proof.
  split.
  unfold beq_ascii.
  case_eq (compare_ascii a b).
  + intros.
    apply compare_ascii_implies_equality with (a := a) (b := b) in H.
    rewrite H.
    reflexivity.
  + intros.
    contradict H0.
    intuition.
  + intros.
    contradict H0.
    intuition.
  + intros.
    rewrite H.
    rewrite beq_ascii_reflexive.
    reflexivity.
Qed.

(** Prove that beq_ascii is transitive. *)
Theorem beq_ascii_transitive : forall (a b c : ascii),
    beq_ascii a b = true /\ beq_ascii b c = true -> beq_ascii a c = true.
Proof.
  intros.
  rewrite beq_ascii_iff_equality in H.
  rewrite beq_ascii_iff_equality in H.
  elim H. (* Elim will split the conjunction in H then introduce the hypotheses to the goal. *)
  intros.
  (* decompose [and] H. *) (* This tactic can also be used to decompose the conjunction in H directly. *)
  rewrite H0.
  rewrite H1.
  rewrite beq_ascii_reflexive.
  reflexivity.
Qed.

(* Boolean less than for ASCII characters. *)
Definition blt_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Lt => true
    | _ => false
  end.

(** Prove that boolean less than for ASCII characters is antireflexive. *)
Theorem blt_ascii_antireflexive : forall (a : ascii),
  blt_ascii a a = false.
Proof.
  intros.
  unfold blt_ascii.
  rewrite compare_ascii_reflexive.
  reflexivity.
Qed.

(** Prove that boolean less than for ASCII characters is asymmetric. *)
Theorem blt_ascii_asymmetric : forall (a b : ascii),
    blt_ascii a b = true -> blt_ascii b a = false.
Proof.
  intros a b.
  unfold blt_ascii.
  case_eq (compare_ascii a b).
  + intros.
    contradict H0. (* Contradiction, if blt_ascii a b = true then compare_ascii a b <> Eq. *)
    intuition.
  + intros.
    rewrite compare_ascii_lt_gt_asymmetric in H.
    rewrite H.
    reflexivity.
  + intros.
    contradict H0. (* Contradiction, if blt_ascii a b = true then compare_ascii a b <> Gt. *)
    intuition.
Qed.

(* TODO: blt_ascii_transitive *)

(* Boolean less than or equal to for ASCII characters. *)
Definition bleq_ascii (a b : ascii) : bool :=
  orb (blt_ascii a b) (beq_ascii a b).

(* Prove that boolean less than or equal to for ASCII characters is reflexive. *)
Theorem bleq_ascii_reflexive : forall (a : ascii),
    bleq_ascii a a = true.
Proof.
  intros.
  unfold bleq_ascii.
  rewrite beq_ascii_reflexive.
  intuition. (* We end up with a disjunction with true = true, solved by intuition. *)
Qed.

(* Boolean greater than for ASCII characters. *)
Definition bgt_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Gt => true
    | _ => false
  end.

(** Prove that boolean greater than for ASCII characters is antireflexive. *)
Theorem bgt_ascii_antireflexive : forall (a : ascii),
    bgt_ascii a a = false.
Proof.
  intros.
  unfold bgt_ascii.
  rewrite compare_ascii_reflexive.
  reflexivity.
Qed.

(** Prove that boolean greater than for ASCII characters is asymmetric. *)
Theorem bgt_ascii_asymmetric : forall (a b : ascii),
    bgt_ascii a b = true -> bgt_ascii b a = false.
Proof.
  intros a b.
  unfold bgt_ascii.
  case_eq (compare_ascii a b).
  + intros.
    contradict H0.
    intuition.
  + intros.
    contradict H0.
    intuition.
  + intros.
    rewrite <- compare_ascii_lt_gt_asymmetric in H.
    rewrite H.
    reflexivity.
Qed.

(* TODO: bgt_ascii_transitive *)

(* Boolean greater than or equal to for ASCII characters. *)
Definition bgeq_ascii (a b : ascii) : bool :=
  orb (bgt_ascii a b) (beq_ascii a b).

(** Prove that boolean greater than or equal to for ASCII characters is reflexive. *)
Theorem bgeq_ascii_reflexive : forall (a : ascii),
    bgeq_ascii a a = true.
Proof.
  intros.
  unfold bgeq_ascii.
  rewrite beq_ascii_reflexive.
  intuition.
Qed.

(* TODO: bgeq_ascii_antisymmetric *)

(* TODO: bgeq_ascii_transitive *)

(* Boolean equality for option ASCII characters. *)
Definition beq_option_ascii (a b : option ascii) : bool :=
  match a, b with
    | None, None => true
    | Some a', Some b' => beq_ascii a' b'
    | _, _ => false
  end.

(* TODO: Proofs for beq_option_ascii. *)

(* Equality notations module for ASCII characters. *)
Module AsciiEqualityNotations.
  
  (* Boolean equality operator. *)
  Notation "a ==_a b" := (beq_ascii a b) (at level 30).

  (* Boolean equality operator (including option). *)
  Notation "a ?==_a b" := (beq_option_ascii a b) (at level 30).

  (* Boolean less than operator. *)
  Notation "a <_a b" := (blt_ascii a b) (at level 30).

  (* Boolean less than or equal to operator. *)
  Notation "a <=_a b" := (bleq_ascii a b) (at level 30).

  (* Boolean greater than operator. *)
  Notation "a >_a b" := (bgt_ascii a b) (at level 30).

  (* Boolean greater than or equal to operator. *)
  Notation "a >=_a b" := (bgeq_ascii a b) (at level 30).

End AsciiEqualityNotations.
