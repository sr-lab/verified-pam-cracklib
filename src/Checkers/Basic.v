Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

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

(* Utility functions to deal with old passwords (that might not exist). *)
Definition is_undefined (old_pwd : option Password) : bool :=
  match old_pwd with
  | None => true
  | Some str => false
  end.

Definition get_pwd (old_pwd : option Password) : Password :=
  match old_pwd with
  | None => "THIS SHOULD NEVER HAPPEN"
  | Some str => str
  end.

Definition old_pwd (pt : PasswordTransition) : option Password :=
  match pt with
   | PwdTransition old new => old
  end.

Definition new_pwd (pt : PasswordTransition) : Password :=
  match pt with
   | PwdTransition old new => new
  end.



(* Notations for checkers. *)
Module CheckerNotations.
  Notation DISABLE_CHECK := None.
  Notation GOODPWD := None.
  Notation "BADPWD: msg" := (Some msg) (at level 80).
  Notation "'NEEDS' oldPwd statement" := (if (is_undefined oldPwd) then DISABLE_CHECK else statement) (at level 80).
  Notation "'NEEDS_OLD_PWD' '(' pt ')' statement" := (if (is_undefined(old_pwd(pt))) then DISABLE_CHECK else statement) (at level 80).
End CheckerNotations.

Import CheckerNotations.

(* Some Basic Checkers *)

(* The new password must be different from old password *)
Definition diff_from_old_pwd (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  NEEDS old_pwd
        if (get_pwd old_pwd) ==_s new_pwd then
          BADPWD: "The new password is the same as the old password"
        else
          GOODPWD.

(* We can implement checkers by specifying password transitions as arguments. *)
Definition diff_from_old_pwd_pt (pt : PasswordTransition) : CheckerResult :=
  NEEDS_OLD_PWD( pt )
        if (get_pwd(old_pwd(pt))) ==_s new_pwd(pt) then
          BADPWD: "The new password is the same as the old password"
        else
          GOODPWD.
 
(* The new password must not be a prefix of the old password (and vice-versa) *)
Definition prefix_of_old_pwd (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  NEEDS old_pwd
        if orb (prefix (get_pwd old_pwd) new_pwd) (prefix new_pwd (get_pwd old_pwd)) then
          BADPWD: "The new password is a prefix of the old password"
        else
          GOODPWD.

(* The new password must not be a palindrome *)
Definition not_palindrome (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  if palindrome new_pwd then
    BADPWD: "The new password is a palindrome."
  else
    GOODPWD.

(* Same checker, but with a password transition as argument *)
Definition not_palindrome_pt (pt : PasswordTransition) : CheckerResult :=
  if palindrome(new_pwd(pt)) then
    BADPWD: "The new password is a palindrome."
  else
    GOODPWD.


(* The new password must not be a rotated version of the old password. *)
Definition not_rotated (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  NEEDS old_pwd
        if string_is_rotated (get_pwd old_pwd) new_pwd then
          BADPWD: "The new password is a rotated version of the old password."
        else
          GOODPWD.

(* The new password must not just contain case changes in relation to the old 
 * password. *)
Definition not_case_changes_only (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  NEEDS old_pwd
        if (string_to_lower (get_pwd old_pwd)) ==_s (string_to_lower new_pwd) then
          BADPWD: "The new password contains case changes only compared to the old password."
        else
          GOODPWD.

(* The new password must have a Levenshtein distance greater than five in 
 * relation to the old password. *)
Definition levenshtein_distance_gt (dist : nat) (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  NEEDS old_pwd
        if leb (levenshtein_distance (get_pwd old_pwd) new_pwd) dist then
          BADPWD: "The new password is too similar to the old password."
        else
          GOODPWD.

(* The new password must be long enough, taking into account number of character 
 * classes. *)
Definition credits_length_check (len : nat) (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  if leb (length new_pwd) (len - (string_count_character_classes new_pwd)) then
    BADPWD: "The new password is too short."
  else
    GOODPWD.
    
