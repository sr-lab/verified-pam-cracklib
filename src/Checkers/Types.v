Require Import Coq.Strings.String.

(* Types *)
Definition ErrorMsg := string.
Definition CheckerResult := option ErrorMsg.
Definition Password := string.
Definition PasswordTransition := option Password -> Password.


