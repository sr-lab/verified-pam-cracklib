Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.

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

(* TODO: Symmetry of compare_ascii_eq? *)

(* TODO: Transitivity of compare_ascii_eq? *)

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

(* TODO: Symmetry of beq_ascii? *)
Lemma beq_ascii_symmetric : forall (a b : ascii),
    beq_ascii a b = beq_ascii b a.
Proof.
  Admitted. (* Obviously true, but requires work. *)

(* TODO: Transitivity of beq_ascii? *)

(* Boolean less than for ASCII characters. *)
Definition blt_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Lt => true
    | _ => false
  end.

(* Boolean less than or equal to for ASCII characters. *)
Definition bleq_ascii (a b : ascii) : bool :=
  orb (blt_ascii a b) (beq_ascii a b).

(* Boolean greater than for ASCII characters. *)
Definition bgt_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Gt => true
    | _ => false
  end.

(* Boolean greater than or equal to for ASCII characters. *)
Definition bgeq_ascii (a b : ascii) : bool :=
  orb (bgt_ascii a b) (beq_ascii a b).

(* TODO: Proofs for blt_ascii, bleq_ascii, bgt_ascii, bgeq_ascii. *)

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
