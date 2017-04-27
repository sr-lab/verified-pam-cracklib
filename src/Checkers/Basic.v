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
Definition old_is_undefined (pt : PasswordTransition) : bool :=
  match pt with
  | PwdTransition old new =>
	match old with
	 | None => true
	 | Some str => false
	end
  end.

(* new_pwd extracts the new password from a password transition *)
Definition new_pwd (pt : PasswordTransition) : Password :=
  match pt with
   | PwdTransition old new => new
  end.



(* Notations for checkers. *)
Module CheckerNotations.
  Notation DISABLE_CHECK := None.
  Notation GOODPWD := None.
  Notation "BADPWD: msg" := (Some msg) (at level 80).
  Notation "'NEEDS' old_pwd 'FROM' pt statement" := (let old_pwd := (fun (pt:PasswordTransition) => (match pt with (PwdTransition old new) => (match old with | None => "" | Some str => str end) end)) in if (old_is_undefined(pt)) then DISABLE_CHECK else statement) (at level 80).
End CheckerNotations.

Import CheckerNotations.


(* Some Basic Checkers *)

(* The new password must be different from old password *)
Definition diff_from_old_pwd (pt : PasswordTransition) : CheckerResult :=
  NEEDS old_pwd FROM pt
        if old_pwd(pt) ==_s new_pwd(pt) then
          BADPWD: "The new password is the same as the old password"
        else
          GOODPWD.
 
(* The new password must not be a prefix of the old password (and vice-versa) *)
Definition prefix_of_old_pwd (pt : PasswordTransition) : CheckerResult :=
  NEEDS old_pwd FROM pt
        if orb (prefix (old_pwd pt) (new_pwd pt)) (prefix (new_pwd pt) (old_pwd pt)) then
          BADPWD: "The new password is a prefix of the old password"
        else
          GOODPWD.

(* The new password must not be a palindrome *)
Definition not_palindrome (pt : PasswordTransition) : CheckerResult :=
  if palindrome (string_to_lower (new_pwd pt)) then
    BADPWD: "The new password is a palindrome."
  else
    GOODPWD.

(* The new password must not be a rotated version of the old password. *)
Definition not_rotated (pt : PasswordTransition) : CheckerResult :=
  NEEDS old_pwd FROM pt
		if string_is_rotated (string_to_lower (old_pwd pt)) (string_to_lower (new_pwd pt)) then
		  BADPWD: "The new password is a rotated version of the old password."
		else
		  GOODPWD.

(* The new password must not just contain case changes in relation to the old 
 * password. *)
Definition not_case_changes_only (pt : PasswordTransition) : CheckerResult :=
  NEEDS old_pwd FROM pt
        if (string_to_lower (old_pwd pt)) ==_s (string_to_lower (new_pwd pt)) then
          BADPWD: "The new password contains case changes only compared to the old password."
        else
          GOODPWD.

(* The new password must have a Levenshtein distance greater than five in 
 * relation to the old password. *)
Definition levenshtein_distance_gt (dist : nat) (pt : PasswordTransition) : CheckerResult :=
  NEEDS old_pwd FROM pt
        if leb (levenshtein_distance (string_to_lower (old_pwd pt)) (string_to_lower (new_pwd pt))) dist then
          BADPWD: "The new password is too similar to the old password."
        else
          GOODPWD.

(* The new password must be long enough, taking into account number of character 
 * classes. *)
Definition credits_length_check (len : nat) (pt : PasswordTransition) : CheckerResult :=
  if leb (length (new_pwd pt)) (len - (string_count_character_classes (new_pwd pt))) then
    BADPWD: "The new password is too short."
  else
    GOODPWD.

(* The new password must be long enough. *)
Definition plain_length_check (len : nat) (pt : PasswordTransition) : CheckerResult :=
  if leb (length (new_pwd pt)) len then
    BADPWD: "The new password is too short."
  else
    GOODPWD.

(* Prove that plain_length_check is correct for all lengths and password transitions. *)
Lemma plain_length_check_correct : forall (len : nat) (pt : PasswordTransition),
  plain_length_check len pt = GOODPWD <-> is_true (negb (leb (length (new_pwd pt)) len)).
Proof.
  intros.
  split.
  + unfold plain_length_check.
    destruct (leb (length (new_pwd pt)) len).
    (* Case 1: Premise is false. *)
    - simpl. congruence.
    (* Case 2: Trivial. *)
    - auto.
  + unfold plain_length_check.
    destruct (leb (length (new_pwd pt)) len).
    - unfold is_true. simpl. congruence.
    - unfold is_true. simpl. auto.
Qed.

(* The new password must not contain more than a certain number of characters of
 * the same class in a row. *)
Definition max_class_repeat (m : nat) (pt : PasswordTransition) : CheckerResult :=
  if leb m (sequence_of (new_pwd pt) is_same_class 0) then
    GOODPWD
  else
    BADPWD: "The new password contains too many of the same character class in a row".


(* Some proofs on the behaviour of checkers (not the functional logic) *)

Definition old_pwd_is_undefined (pt : PasswordTransition): bool :=
  match pt with
  | PwdTransition old _ =>
    match old with
    | None => true
    | Some _ => false
    end
  end.


(* If the old password is undefined, then the checker prefix_of_old_pwd 
   accepts any password (i.e. the prefix check is essentially disabled). *)
Lemma prefix_old_pwd_undefined: forall (pt: PasswordTransition),
    old_pwd_is_undefined(pt) = true -> prefix_of_old_pwd(pt) = GOODPWD.
Proof.
  intros.
  unfold old_pwd_is_undefined in H. 
  (* Case analysis *)
  destruct pt. destruct o.
   (* Case 1 (trivial): old password is defined *)
   - congruence.
   (* Case 2: old password is undefined *)
   - unfold prefix_of_old_pwd. simpl. auto.
Qed.