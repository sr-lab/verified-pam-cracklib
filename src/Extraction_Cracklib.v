(* Import functions from framework. *)
Require Import Pamba.Bool.Bool.
Require Import Pamba.String.Distance.
Require Import Pamba.String.Search.
Require Import Pamba.String.Sequence.
Require Import Pamba.String.Palindrome.

(* The following imports are useful for extracting Haskell code. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

(* Define functions used in pam_cracklib. *)

Definition palindrome_c (s : string) : nat :=
  nat_of_bool (palindrome h n).

Definition wordcheck_c (h n : string) : nat :=
  nat_of_bool (contains h n).

Definition minclass_c (s : string) (m : nat) : nat :=
  nat_of_bool (negb (ltb (string_count_character_classes s) m)).

Definition sequence_c (s : string) (m : nat) : nat :=
  nat_of_bool (leb m (max (sequence_up s) (sequence_down s))).

Definition consecutive_c (s : string) (m : nat) : nat :=
  nat_of_bool (leb m (sequence_eq s)).

Definition similar_c (a b : string) (d : nat) : nat :=
  nat_of_bool (negb (ltb (levenshtein_distance a b) d)).

Extraction Language Haskell.
Extraction "PamGenerated.hs" palindrome_c wordcheck_c minclass_c sequence_c consecutive_c similar_c.
