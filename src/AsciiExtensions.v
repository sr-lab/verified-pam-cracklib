Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

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
