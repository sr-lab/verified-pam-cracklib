Require Import Coq.Strings.String.

(* ErrorMsg (error message) is an alias of string. *)
Definition ErrorMsg := string.

(* The result of a checker checking a password. *)
Definition CheckerResult := option ErrorMsg.

(* Password is an alias of string. *)
Definition Password := string.

(* A password transition represents an (optional) old password being changed to
 * a new password . *)
Inductive PasswordTransition : Set := 
	PwdTransition :  (option Password) -> Password -> PasswordTransition.
