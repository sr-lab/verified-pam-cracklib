# Proofs Overview
An overview of proofs across the project. Proofs marked as incomplete still need to be added/completed. This list does not include proofs yet to be identified.

## Ascii/Class.v
Contains functions (and corresponding proofs) for ASCII character class checking/manipulation.
### is_lower (c : ascii)
No proofs identified.
### is_upper (c : ascii)
No proofs identified.
### is_digit (c : ascii)
No proofs identified.
### is_other (c : ascii)
No proofs identified.
### is_same_class (c1 c2 : ascii)
No proofs identified.
### to_lower (c : ascii)
No proofs identified.
### to_upper (c : ascii)
No proofs identified.

## Ascii/Equality.v
Contains functions (and corresponding proofs) for ASCII character comparison.
### compare_ascii (a b : ascii)
Foundation for proofs based in comparison.
+ compare_ascii_implies_equality
+ compare_ascii_reflexivie
+ compare_ascii_eq_symmetric
+ compare_ascii_lt_gt_asymmetric
+ compare_ascii_eq_transitive
### beq_ascii (a b : ascii)
Proof of correctness of boolean ASCII equality function by property (`==_a` operator). 
+ beq_ascii_reflexive
+ beq_ascii_symmetric
+ beq_ascii_iff_equality
+ beq_ascii_transitive
### blt_ascii (a b : ascii)
Proof of correctness of boolean ASCII less-than function by property (`<_a` operator).
+ blt_ascii_antireflexive
+ blt_ascii_asymmetric
+ blt_ascii_transitive **INCOMPLETE**
### bleq_ascii (a b : ascii)
Proof of correctness of boolean ASCII less-than-or-equal-to function by property (`<=_a` operator).
+ bleq_ascii_reflexive
+ bgeq_ascii_antisymmetric **INCOMPLETE**
+ bgeq_ascii_transitive **INCOMPLETE**
### bgt_ascii (a b : ascii)
Proof of correctness of boolean ASCII greater-than function by property (`>_a` operator). 
+ bgt_ascii_antireflexive
+ bgt_ascii_asymmetric
+ bgt_ascii_transitive **INCOMPLETE**
### bgeq_ascii (a b : ascii)
Proof of correctness of boolean ASCII greater-than-or-equal-to function by property (`>=_a` operator). 
+ bgeq_ascii_reflexive
+ bgeq_ascii_antisymmetric **INCOMPLETE**
+ bgeq_ascii_transitive **INCOMPLETE**
### beq_option_ascii (a b : option ascii)
Proof of correctness of boolean option ASCII equality function by property (`?==_a` operator). 
+ beq_option_ascii_reflexive **INCOMPLETE**
+ beq_option_ascii_symmetric **INCOMPLETE**
+ beq_option_ascii_iff_equality **INCOMPLETE**
+ beq_option_ascii_transitive **INCOMPLETE**

## Bool/Bool.v
Contains functions (and corresponding proofs) for manipulation of boolean values.
### nat_of_bool (b : bool)
No proofs identified.

## Checkers/Basic.v
### old_is_undefined (pt : PasswordTransition)
No proofs identified.
### new_pwd (pt : PasswordTransition)
No proofs identified.
### diff_from_old_pwd (pt : PasswordTransition)
+ diff_from_old_pwd_correct
### prefix_of_old_pwd (pt : PasswordTransition)
+ prefix_of_old_pwd_correct
+ prefix_old_pwd_undefined
### not_palindrome (pt : PasswordTransition)
+ not_palindrome_correct 
### not_case_changes_only (pt : PasswordTransition)
+ not_case_changes_only_correct
### levenshtein_distance_gt (pt : PasswordTransition)
+ levenshtein_distance_gt_correct
### credits_length_check (pt : PasswordTransition)
+ credits_length_check_correct
### plain_length_check (pt : PasswordTransition)
+ plain_length_check_correct
### max_class_repeat (pt : PasswordTransition)
+ max_class_repeat_correct
### old_pwd_is_undefined
No proofs identified.

## String/Distance.v
### hamming_distance (a b : string)
+ hamming_distance_undefined_for_different_lengths **INCOMPLETE**
+ hamming_distance_defined_for_same_length **INCOMPLETE**
+ hamming_distance_zero_for_identical
+ hamming_distance_at_most_string_length **INCOMPLETE**
### indicator (a b : string) (i j : nat)
No proofs identified.
### levenshtein (a b : string) (i j n : nat)
No proofs identified.
### levenshtein_distance (a b : string)
+ levenshtein_distance_at_least_length_diff **INCOMPLETE**
+ levenshtein_distance_zero_for_equal_strings **INCOMPLETE**
+ levenshtein_distance_same_length_leq_hamming **INCOMPLETE**
+ levenshtein_distance_leq_longer_string_length **INCOMPLETE**
+ levenshtein_distance_triangle_inequality **INCOMPLETE**
### palindrome (s : string)
+ palindrome_correct
### palindrome_efficient_recursive (s : string) (x y : nat)
No proofs identified.
### palindrome_efficient (s : string)
No proofs identified.

## String/Search.v
### contains (h n : string)
No proofs identified.
### string_count (s : string) (f : ascii->bool)
No proofs identified.
### string_count_lower (s : string)
No proofs identified.
### string_count_upper (s : string)
No proofs identified.
### string_count_digit (s : string)
No proofs identified.
### string_count_other (s : string)
No proofs identified.
### string_contains (s : string) (f : string->nat)
No proofs identified.
### string_contains_lower (s : string)
No proofs identified.
### string_contains_upper (s : string)
No proofs identified.
### string_contains_digit (s : string)
No proofs identified.
### string_contains_other (s : string)
No proofs identified.
### string_count_character_classes (s : string)
No proofs identified.
### string_is_rotated (a b : string)
No proofs identified.

## String/Sequence.v
### consecutive_up (c1 c2 : ascii)
No proofs identified.
### consecutive_down (c1 c2 : ascii)
No proofs identified.
### sequence_of (s : string) (f : ascii->ascii->bool) (a : nat)
No proofs identified.
### sequence_up (s : string)
No proofs identified.
### sequence_down (s : string)
No proofs identified.
### sequence_eq (s : string)
No proofs identified.

## String/Transform.v
### string_to_lower (s : string)
No proofs identified.
### string_to_upper (s : string)
No proofs identified.
### string_reverse (s : string)
+ append_empty_reflexive
+ append_associative
+ string_reverse_append_distributive
+ string_reverse_unit
+ strinng_reverse_involutive
