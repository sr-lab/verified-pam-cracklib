Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Local Open Scope string_scope.

(* Import functions from framework. *)
Require Import Hapsl.Checkers.Types.
Require Import Hapsl.Checkers.Basic.
Require Import Hapsl.String.Search.
Require Import Hapsl.String.Equality.

Import CheckerNotations.
Import StringEqualityNotations.

(* Users can define their own checkers here. *)

(* Define password quality policy. *)
Definition pwd_quality_policy :=
  [
      diff_from_old_pwd
    ; not_palindrome
    ; not_rotated
    ; not_case_changes_only
    ; levenshtein_distance_gt 5
    ; credits_length_check 8
  ].
