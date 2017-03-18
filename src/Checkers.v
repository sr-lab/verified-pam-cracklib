Require Import Coq.Lists.List.
Import ListNotations.

(* Import functions from framework. *)
Require Import Hapsl.Bool.Bool.
Require Import Hapsl.String.Distance.
Require Import Hapsl.String.Search.
Require Import Hapsl.String.Sequence.
Require Import Hapsl.String.Palindrome.

Require Import Hapsl.String.Equality.
Import StringEqualityNotations.


Require Import Coq.Strings.String.
Open Local Scope string_scope.

(* Types *)
Definition ErrorMsg := string.
Definition CheckerResult := option ErrorMsg.
Definition Password := string.
Definition PasswordTransition := option Password -> Password.

(* Notations *)
Notation DISABLE_CHECK := None.
Notation GOODPWD := None.
Notation "BADPWD: msg" := (Some msg) (at level 80).

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

Notation "'NEEDS' oldPwd statement" := (if (is_undefined oldPwd) then DISABLE_CHECK else statement) (at level 80).

(* Examples of checkers *)
Definition diffFromOldPwd (oldPwd: option Password) (newPwd : Password): CheckerResult :=
 NEEDS oldPwd 
  if ((get_pwd oldPwd) ==_s newPwd) 
  then BADPWD: "The new password is the same as the old password"
  else GOODPWD.
 
Definition prefixOfOldPwd (oldPwd: option Password) (newPwd : Password): CheckerResult :=
 NEEDS oldPwd 
  if (orb (prefix (get_pwd oldPwd) newPwd) (prefix newPwd (get_pwd oldPwd)))
  then BADPWD: "The new password is a prefix of the old password"
  else GOODPWD.

Definition newPwdContainsDigits (oldPwd: option Password) (newPwd: Password) : CheckerResult :=
 if (string_contains_digit newPwd)
 then BADPWD: "The new password contains digits"
 else GOODPWD.

Definition allGood (oldPwd: option Password) (newPwd : Password): CheckerResult := GOODPWD.

Definition notPalindrome (oldPwd: option Password) (newPwd: Password) : CheckerResult :=
 if (palindrome newPwd) 
 then BADPWD: "The new password is a palindrome." 
 else GOODPWD.


(* Define checkers that will be exported *)
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

Check pwd_quality_policy.
