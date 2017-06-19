# Proofs Overview
An overview of proofs across the project.

## Ascii/Class.v
+ is_lower (c : ascii)
+ is_upper (c : ascii)
+ is_digit (c : ascii)
+ is_other (c : ascii)
+ is_same_class (c1 c2 : ascii)
+ to_lower (c : ascii)
+ to_upper (c : ascii)

## Ascii/Equality.v
+ compare_ascii (a b : ascii)
  - compare_ascii_implies_equlity
  - compare_ascii_reflexivie
  - compare_ascii_eq_symmetric
  - compare_ascii_lt_gt_asymmetric
  - compare_ascii_eq_transitive
+ beq_ascii (a b : ascii)
  - beq_ascii_reflexive
  - beq_ascii_symmetric
  - beq_ascii_iff_equality
  - beq_ascii_transitive
+ blt_ascii (a b : ascii)
  - blt_ascii_antireflexive
  - blt_ascii_asymmetric
  - blt_ascii_transitive **INCOMPLETE**
+ bleq_ascii (a b : ascii)
  - bleq_ascii_reflexive
  - bgeq_ascii_antisymmetric **INCOMPLETE**
  - bgeq_ascii_transitive **INCOMPLETE**
+ bgt_ascii (a b : ascii)
  - bgt_ascii_antireflexive
  - bgt_ascii_asymmetric
  - bgt_ascii_transitive **INCOMPLETE**
+ bgeq_ascii (a b : ascii)
  - bgeq_ascii_reflexive
  - bgeq_ascii_antisymmetric **INCOMPLETE**
  - bgeq_ascii_transitive **INCOMPLETE**
+ beq_option_ascii (a b : option ascii)

## Bool/Bool.v
+ nat_of_bool (b : bool)

## Checkers/Basic.v
+ old_is_undefined (pt : PasswordTransition)
+ new_pwd (pt : PasswordTransition)
+ diff_from_old_pwd (pt : PasswordTransition)
  - diff_from_old_pwd_correct
+ prefix_of_old_pwd (pt : PasswordTransition)
  - prefix_of_old_pwd_correct
  - prefix_old_pwd_undefined
+ not_palindrome (pt : PasswordTransition)
  - not_palindrome_correct 
+ not_case_changes_only (pt : PasswordTransition)
  - not_case_changes_only_correct
+ levenshtein_distance_gt (pt : PasswordTransition)
  - levenshtein_distance_gt_correct
+ credits_length_check (pt : PasswordTransition)
  - credits_length_check_correct
+ plain_length_check (pt : PasswordTransition)
  - plain_length_check_correct
+ max_class_repeat (pt : PasswordTransition)
  - max_class_repeat_correct
+ old_pwd_is_undefined

## String/Distance.v
+ hamming_distance (a b : string)
  - hamming_distance_undefined_for_different_lengths **INCOMPLETE**
  - hamming_distance_defined_for_same_length **INCOMPLETE**
  - hamming_distance_zero_for_identical
  - hamming_distance_at_most_string_length **INCOMPLETE**
+ indicator (a b : string) (i j : nat)
+ levenshtein (a b : string) (i j n : nat)
+ levenshtein_distance (a b : string)
  - levenshtein_distance_at_least_length_diff **INCOMPLETE**
  - levenshtein_distance_zero_for_equal_strings **INCOMPLETE**
  - levenshtein_distance_same_length_leq_hamming **INCOMPLETE**
  - levenshtein_distance_leq_longer_string_length **INCOMPLETE**
  - levenshtein_distance_triangle_inequality **INCOMPLETE**
+ palindrome (s : string)
  - palindrome_correct
+ palindrome_efficient_recursive (s : string) (x y : nat)
+ palindrome_efficient (s : string)

## String/Search.v
+ contains (h n : string)
+ string_count (s : string) (f : ascii->bool)
+ string_count_lower (s : string)
+ string_count_upper (s : string)
+ string_count_digit (s : string)
+ string_count_other (s : string)
+ string_contains (s : string) (f : string->nat)
+ string_contains_lower (s : string)
+ string_contains_upper (s : string)
+ string_contains_digit (s : string)
+ string_contains_other (s : string)
+ string_count_character_classes (s : string)
+ string_is_rotated (a b : string)

## String/Sequence.v
+ consecutive_up (c1 c2 : ascii)
+ consecutive_down (c1 c2 : ascii)
+ sequence_of (s : string) (f : ascii->ascii->bool) (a : nat)
+ sequence_up (s : string)
+ sequence_down (s : string)
+ sequence_eq (s : string)

## String/Transform.v
+ string_to_lower (s : string)
+ string_to_upper (s : string)
+ string_reverse (s : string)
  - append_empty_reflexive
  - append_associative
  - string_reverse_append_distributive
  - string_reverse_unit
  - strinng_reverse_involutive
