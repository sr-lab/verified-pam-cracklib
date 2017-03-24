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

(* Examples: User-defined checkers. *)

(* The most useless checker: all passwords are good passwords :-) *)
Definition all_good (old_pwd : option Password) (new_pwd : Password) : CheckerResult := GOODPWD.

(* Define password quality policy. *)
Definition pwd_quality_policy :=
  [
      diff_from_old_pwd
    ; not_palindrome
    ; not_rotated
    ; not_case_changes_only
    ; levenshtein_distance_gt 5
    ; credits_length_check 8
    (* TODO: confirm that we can remove the following two checkers:
      ; prefix_of_old_pwd
      ; all_good
    *)
  ].
