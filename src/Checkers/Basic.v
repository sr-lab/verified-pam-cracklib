(* Import functions from framework. *)
Require Import Hapsl.Bool.Bool.
Require Import Hapsl.String.Palindrome.
Require Import Hapsl.String.Equality.
Import StringEqualityNotations.

(* Import types from framework. *)
Require Import Hapsl.Checkers.Types.

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
