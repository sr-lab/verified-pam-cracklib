Require Import Coq.NArith.NArith.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.

(* Returns the comparison of two ASCII characters. *)
Definition compare_ascii (c1 c2 : ascii) : comparison  :=
  N.compare (N_of_ascii c1) (N_of_ascii c2).

(* Proves that a comparison of two ASCII characters implies their equality. *)
Lemma compare_ascii_implies_eq : forall (c1 c2 : ascii),
  compare_ascii c1 c2 = Eq -> c1 = c2.
Proof.
  intros.
  rewrite <- ascii_N_embedding with (a := c1).
  rewrite <- ascii_N_embedding with (a := c2).
  f_equal.
  now apply N.compare_eq_iff.
Qed.

(* Boolean equality for ASCII characters. *)
Definition beq_ascii (c1 c2 : ascii) : bool :=
  match compare_ascii c1 c2 with
    | Eq => true
    | _ => false
  end.

(* Boolean equality for option ASCII characters. *)
Definition beq_option_ascii (c1 c2 : option ascii) : bool :=
  match c1, c2 with
    | None, None => true
    | Some c1', Some c2' => beq_ascii c1' c2'
    | _, _ => false
  end.

(* Returns true if a given ASCII character is upper case, otherwise returns 
   false. *)
Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (leb 97 n) (leb n 122).

(* Returns true if a given ASCII character is lower case, otherwise returns 
   false. *)
Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (leb 65 n) (leb n 90).

(* Returns true if a given ASCII character is a digit, otherwise returns 
   false. *)
Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (leb 48 n) (leb n 57).

(* Returns true if a given ASCII character is neither a digit, upper case letter
   nor lower case letter. Otherwise returns false. *)
Definition is_other (c : ascii) : bool :=
  negb (orb (is_lower c) (orb (is_upper c) (is_digit c))).

(* Returns true if two given ASCII characters belong to the same character 
   class, otherwise returns false. *)
Definition is_same_class (c1 c2 : ascii) : bool :=
  ((is_lower c1) && (is_lower c2))
  || ((is_upper c1) && (is_upper c2))
  || ((is_digit c1) && (is_digit c2))
  || ((is_other c1) && (is_other c2)).

(* Converts an upper case ASCII characer to lower case. For any other character
   returns it unchanged. *)
Definition to_lower (c : ascii) : ascii :=
  let n := nat_of_ascii c in
    if is_upper c then
      ascii_of_nat (n + 32)
    else
      c.

(* Converts a lower case ASCII character to upper case. For any other character
   returns it unchanged. *)
Definition to_upper (c : ascii) : ascii :=
  let n := nat_of_ascii c in
    if is_lower c then
      ascii_of_nat (n - 32)
    else
      c.