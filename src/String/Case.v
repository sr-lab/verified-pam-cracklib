Require Import Coq.Strings.String.

Require Import Pamba.Ascii.Class.

(* Converts a string to lower case. *)
Fixpoint string_to_lower (s : string) : string :=		
  match s with
  | EmptyString => s
  | String c s => String (to_lower c) (string_to_lower s)
  end.

(* Converts a string to upper case. *)
Fixpoint string_to_upper (s : string) : string :=
  match s with
  | EmptyString => s
  | String c s => String (to_upper c) (string_to_upper s)
  end.
