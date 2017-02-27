Require Import Coq.NArith.NArith.
Require Import Coq.Strings.Ascii.

(* Returns the comparison of two ASCII characters. *)
Definition compare_ascii (a b : ascii) : comparison  :=
  N.compare (N_of_ascii a) (N_of_ascii b).

(* Boolean equality for ASCII characters. *)
Definition beq_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Eq => true
    | _ => false
  end.

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

(* Boolean equality for option ASCII characters. *)
Definition beq_option_ascii (a b : option ascii) : bool :=
  match a, b with
    | None, None => true
    | Some a', Some b' => beq_ascii a' b'
    | _, _ => false
  end.

(* Equality notations module for ASCII characters. *)
Module AsciiEqualityNotations.

  (* Boolean equality operator. *)
  Notation "a ==_a b" := (beq_ascii a b) (at level 30).

  (* Boolean equality operator (including option). *)
  Notation "a ?==_a b" := (beq_option_ascii a b) (at level 30).

  (* Boolean less than operator. *)
  Notation "a <_a b" := (blt_ascii a b) (at level 30).

  (* Boolean less than or equal to operator. *)
  Notation "a <=_a b" := (orb (blt_ascii a b) (beq_ascii a b)) (at level 30).

  (* Boolean greater than operator. *)
  Notation "a >_a b" := (bgt_ascii a b) (at level 30).

  (* Boolean greater than or equal to operator. *)
  Notation "a >=_a b" := (bgeq_ascii a b) (at level 30).

End AsciiEqualityNotations.
