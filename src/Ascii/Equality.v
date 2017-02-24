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

Notation "a @= b" := (beq_ascii a b) (at level 50).

(* Boolean less than for ASCII characters. *)
Definition blt_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Lt => true
    | _ => false
  end.

Notation "a @< b" := (blt_ascii a b) (at level 50).

(* Boolean greater than for ASCII characters. *)
Definition bgt_ascii (a b : ascii) : bool :=
  match compare_ascii a b with
    | Gt => true
    | _ => false
  end.

Notation "a @> b" := (bgt_ascii a b) (at level 50).

(* Boolean equality for option ASCII characters. *)
Definition beq_option_ascii (a b : option ascii) : bool :=
  match a, b with
    | None, None => true
    | Some a', Some b' => a' @= b'
    | _, _ => false
  end.
