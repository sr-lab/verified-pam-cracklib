Require Import Coq.Strings.Ascii.

Require Import Hapsl.Ascii.Equality.

Import AsciiEqualityNotations.

(* Returns true if a given ASCII character is lower case, otherwise returns 
   false. *)
Definition is_lower (c : ascii) : bool :=
  (c >=_a "a") && (c <=_a "z").

(* Returns true if a given ASCII character is upper case, otherwise returns 
   false. *)
Definition is_upper (c : ascii) : bool :=
  (c >=_a "A") && (c <=_a "Z").

(* Returns true if a given ASCII character is a digit, otherwise returns 
   false. *)
Definition is_digit (c : ascii) : bool :=
  (c >=_a "0") && (c <=_a "9").

(* Returns true if a given ASCII character is neither a digit, upper case letter
   nor lower case letter. Otherwise returns false. *)
Definition is_other (c : ascii) : bool :=
  negb ((is_lower c) || (is_upper c) || (is_digit c)).

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
