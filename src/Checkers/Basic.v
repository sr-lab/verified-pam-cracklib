Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

(* Import functions from framework. *)
Require Import Hapsl.Bool.Bool.
Require Import Hapsl.Ascii.Class.
Require Import Hapsl.String.Distance.
Require Import Hapsl.String.Transform.
Require Import Hapsl.String.Palindrome.
Require Import Hapsl.String.Equality.
Require Import Hapsl.String.Search.
Require Import Hapsl.String.Sequence.

Import StringEqualityNotations.

(* Import types from framework. *)
Require Import Hapsl.Checkers.Types.

(* Utility functions to deal with old passwords (that might not exist). *)
Definition is_undefined (old_pwd : option Password) : bool :=
  match old_pwd with
  | None => true
  | Some str => false
  end.

Definition old_is_undefined (pt : PasswordTransition) : bool :=
  match pt with
  | PwdTransition old new =>
	match old with
	 | None => true
	 | Some str => false
	end
  end.

Definition get_pwd (old_pwd : option Password) : Password :=
  match old_pwd with
  | None => "THIS SHOULD NEVER HAPPEN"
  | Some str => str
  end.


(* old_pwd and new_pwd extract the old and new passwords from a password transition *)
(*
Definition old_pwd (pt : PasswordTransition) : Password :=
  match pt with
   | PwdTransition old new => 
	match old with
	 | None     => "YOU SHOULD USE NEEDS_OLD_PWD"
	 | Some str => str
	end
  end.
*)

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
(*  Notation "'NEEDS_OLD_PWD' '(' pt ')' statement" := (if (old_is_undefined(pt)) then DISABLE_CHECK else statement) (at level 80). *)
  Notation "'NEEDS_' old_pwd 'AA' pt statement" := (let old_pwd := (fun (pt:PasswordTransition) => (match pt with (PwdTransition old new) => (match old with | None => "YOU SHOULD USE NEEDS_OLD_PWD" | Some str => str end) end)) in if (old_is_undefined(pt)) then DISABLE_CHECK else statement) (at level 80).
End CheckerNotations.

Import CheckerNotations.


Definition t : Password :=
 let a := "a" in 
 let f := (fun (x:string) => x) in
 let old_pwd := (fun (pt:PasswordTransition) => (match pt with (PwdTransition old new) => (match old with | None => "YOU SHOULD USE NEEDS_OLD_PWD" | Some str => str end) end)) in
 f(a).


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
  (*let old_pwd := (fun (pt:PasswordTransition) => (match pt with (PwdTransition old new) => (match old with | None => "YOU SHOULD USE NEEDS_OLD_PWD" | Some str => str end) end)) in if (old_is_undefined(pt)) then DISABLE_CHECK else *)
  NEEDS_ old_pwd AA pt
        if old_pwd(pt) ==_s new_pwd(pt) then
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
    
(* The new password must not contain more than a certain number of characters of
 * the same class in a row. *)
Definition max_class_repeat (m : nat) (old_pwd : option Password) (new_pwd : Password) : CheckerResult :=
  if leb m (sequence_of new_pwd is_same_class 0) then
    GOODPWD
  else
    BADPWD: "The new password contains too many of the same character class in a row".
