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
(* ; TODO: Not be a rotated version of the old password, if any. *)
(* ; TODO: Not contain case changes only in relation to the previous password, if any. *)
(* ; TODO: Have a Levenshtein distance of 5 or greater from the previous password, if any. [1] *)
(* ; TODO: Be at least 9 characters long [2], however: see Saul's docs *)
 ; prefixOfOldPwd
 ; newPwdContainsDigits
 ; allGood
 ].
