Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

(* Converts the boolean value true to the natural number 1, false to 0. *)
Fixpoint bool_to_nat(b: bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.

(* Returns true if a given ASCII character is upper case, otherwise returns false. *)
Definition is_lower(c: ascii) : bool :=
  let n := nat_of_ascii c in
    (andb (leb 97 n) (leb n 122)).

(* Returns true if a given ASCII character is lower case, otherwise returns false. *)
Definition is_upper(c: ascii) : bool :=
  let n := nat_of_ascii c in
    (andb (leb 65 n) (leb n 90)).

(* Returns true if a given ASCII character is a digit, otherwise returns false. *)
Definition is_digit(c: ascii) : bool :=
  let n := nat_of_ascii c in
    (andb (leb 48 n) (leb n 57)).

(* Returns true if a given ASCII character is neither a digit, upper or lower, otherwise returns false. *)
Definition is_other(c: ascii) : bool :=
  (negb (orb (is_lower c) (orb (is_upper c) (is_digit c)))).

(* Converts an ASCII characer to lower case. *)
Definition to_lower(c: ascii) : ascii :=
  let n := nat_of_ascii c in
    if is_upper c then
      ascii_of_nat (n + 32)
    else
      c.

(* Converts an ASCII character to upper case. *)
Definition to_upper(c: ascii) : ascii :=
  let n := nat_of_ascii c in
    if is_lower c then
      ascii_of_nat (n - 32)
    else
      c.

(* Converts a string to lower case. *)
Fixpoint string_to_lower(s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_lower c) (string_to_lower s)
  end.

(* Converts a string to upper case. *)
Fixpoint string_to_upper(s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_upper c) (string_to_upper s)
  end.

(* Returns true if two strings are equivalent, otherwise returns false. *)
Fixpoint string_eq(s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, EmptyString => true
  | String c1 s1', String c2 s2' => andb
    (beq_nat (nat_of_ascii c1) (nat_of_ascii c2)) (string_eq s1' s2')
  | _, _ => false
  end.

(* Returns true if two strings are equivalent, disregarding case, otherwise returns false. *)
Fixpoint string_eq_ignorecase(s1 s2 : string) : bool :=
  (string_eq (string_to_lower s1) (string_to_lower s2)).

Fixpoint string_count(s : string) (f: ascii->bool) : nat :=
  match s with
  | EmptyString => 0
  | String c s => (add (bool_to_nat (f c)) (string_count s f))
  end.

(* Returns the number of lower case letters in a string. *)
Fixpoint string_count_lower(s : string) : nat :=
  (string_count s is_lower).

(* Returns the number of upper case letters in a string. *)
Fixpoint string_count_upper(s : string) : nat :=
  (string_count s is_upper).

(* Returns the number of digits in a string. *)
Fixpoint string_count_digits(s : string) : nat :=
  (string_count s is_digit).

(* Returns the number of other characters in a string (that is, not upper, lower or digit). *)
Fixpoint string_count_other(s : string) : nat :=
  (string_count s is_other).

Fixpoint string_contains(s : string) (f: string->nat) : bool :=
  (ltb 0 (f s)).

Fixpoint string_contains_lower(s : string) : bool :=
  (string_contains s string_count_lower).

Fixpoint string_contains_upper(s : string) : bool :=
  (string_contains s string_count_upper).

Fixpoint string_contains_digit(s : string) : bool :=
  (string_contains s string_count_digits).

Fixpoint string_contains_other(s : string) : bool :=
  (string_contains s string_count_other).

Fixpoint string_count_character_classes(s : string) : nat :=
  (bool_to_nat (string_contains_lower s)) 
+ (bool_to_nat (string_contains_upper s)) 
+ (bool_to_nat (string_contains_digit s))
+ (bool_to_nat (string_contains_other s)).

Fixpoint minclass(s : string) (min_class :nat) : bool :=
  (negb (ltb (string_count_character_classes s) min_class)).

(* Demonstration. *)
Compute is_lower "a".
Compute is_lower "Z".
Compute is_upper "a".
Compute is_upper "Z".
Compute to_lower "A".
Compute to_upper "z".
Compute string_to_upper "hello world".
Compute string_to_lower "HELLO WORLD".
Compute string_eq "hello" "hello".
Compute string_eq "hello" "world".
Compute string_eq_ignorecase "HELLO" "hEllo".

(* Pulling together. *)
Compute minclass "absfh27394" 3. (* Fails, lowercase and digit present only, 3 classes required. *)
Compute minclass "absfh27394" 2. (* Passes, lowercase and digit present, 2 classes required. *)
Compute minclass "SDJFS27394" 1. (* Passes, uppercase and digit present, 1 class required. *)
Compute minclass "" 1. (* Fails, empty string, one class required. *)
Compute minclass "" 0. (* Passes, empty string, no classes required. *)
Compute minclass "aB1@@#" 4. (* Passes, contains all 4 character classes, 4 required. *)
