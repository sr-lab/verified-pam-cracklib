Require Import Coq.Lists.List.
Import ListNotations.

(* Import functions from framework. *)
Require Import Hapsl.String.Search. (* Needed for string_contains_digit *)

Require Import Hapsl.String.Equality.
Import StringEqualityNotations.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Hapsl.Checkers.Types.
Require Import Hapsl.Checkers.Basic.
Import CheckerNotations.



(* Examples: user-defined checkers *)

(* The new password must not contain digits *)
Definition newPwdContainsDigits (oldPwd: option Password) (newPwd: Password) : CheckerResult :=
 if (string_contains_digit newPwd)
 then BADPWD: "The new password contains digits"
 else GOODPWD.

(* The most useless checker: all passwords are good passwords :-) *)
Definition allGood (oldPwd: option Password) (newPwd : Password): CheckerResult := GOODPWD.

(* Define password quality policy *)
Definition pwd_quality_policy :=
  [
    diffFromOldPwd
    ; notPalindrome
    ; notRotated
    ; notCaseChangesOnly
    ; levenshteinDistanceGt 5
    ; creditsLengthCheck 8
    ; prefixOfOldPwd
    ; allGood
  ].
