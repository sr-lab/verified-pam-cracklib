(* Import functions from framework. *)
Require Import Hapsl.Bool.Bool.
Require Import Hapsl.String.Distance.
Require Import Hapsl.String.Transform.
Require Import Hapsl.String.Palindrome.
Require Import Hapsl.String.Equality.
Require Import Hapsl.String.Search.
Import StringEqualityNotations.

(* Import types from framework. *)
Require Import Hapsl.Checkers.Types.

Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

(* Util functions to deal with old passwords (that might not exist) *)
Definition is_undefined (oldPwd: option Password) : bool :=
  match oldPwd with
    | None     => true
    | Some str => false
  end.

Definition get_pwd (oldPwd: option Password) : Password :=
  match oldPwd with
    | None     => "THIS SHOULD NEVER HAPPEN"
    | Some str => str
  end.

Module CheckerNotations.
(* Notations *)
 Notation DISABLE_CHECK := None.
 Notation GOODPWD := None.
 Notation "BADPWD: msg" := (Some msg) (at level 80).
 Notation "'NEEDS' oldPwd statement" := (if (is_undefined oldPwd) then DISABLE_CHECK else statement) (at level 80).
End CheckerNotations.
Import CheckerNotations.


(* Some Basic Checkers *)

(* The new password must be different from old password *)
Definition diffFromOldPwd (oldPwd: option Password) (newPwd : Password): CheckerResult :=
 NEEDS oldPwd 
  if ((get_pwd oldPwd) ==_s newPwd) 
  then BADPWD: "The new password is the same as the old password"
  else GOODPWD.
 
(* The new password must not be a prefix of the old password (and vice-versa) *)
Definition prefixOfOldPwd (oldPwd: option Password) (newPwd : Password): CheckerResult :=
 NEEDS oldPwd 
  if (orb (prefix (get_pwd oldPwd) newPwd) (prefix newPwd (get_pwd oldPwd)))
  then BADPWD: "The new password is a prefix of the old password"
  else GOODPWD.

(* The new password must not be a palindrome *)
Definition notPalindrome (oldPwd: option Password) (newPwd: Password) : CheckerResult :=
 if (palindrome newPwd) 
 then BADPWD: "The new password is a palindrome." 
 else GOODPWD.

(* Checks that a new password is not just a rotated version of the old password. *)
Definition notRotated (oldPwd: option Password) (newPwd : Password): CheckerResult :=
  NEEDS oldPwd
        if string_is_rotated (get_pwd oldPwd) newPwd then
          BADPWD: "The new password is a rotated version of the old password"
        else
          GOODPWD.

(* Checks that a new password does not just contain case changes in relation to the old password. *)
Definition notCaseChangesOnly (oldPwd: option Password) (newPwd : Password): CheckerResult :=
  NEEDS oldPwd
        if (string_to_lower (get_pwd oldPwd)) ==_s (string_to_lower newPwd) then
          BADPWD: "The new password contains case changes only compared to the old password"
        else
          GOODPWD.

(* Checks that the new password and old password have a Levenshtein distance greater than five. *)
Definition levenshteinDistanceGtFive (oldPwd: option Password) (newPwd : Password): CheckerResult :=
  NEEDS oldPwd
        if (leb (levenshtein_distance (get_pwd oldPwd) newPwd) 5) then
          BADPWD: "The new password is too similar to the old password"
        else
          GOODPWD.

(* Checks that the new password is long enough, taking into account number of character classes. *)
Definition creditsLengthCheck (oldPwd: option Password) (newPwd : Password): CheckerResult :=
  if leb (length newPwd) (8 - (string_count_character_classes newPwd)) then
    BADPWD: "The new password is too short"
  else
    GOODPWD.
    