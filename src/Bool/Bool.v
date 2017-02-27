(* Converts the boolean value true to the natural number 1, false to 0. *)
Fixpoint nat_of_bool (b : bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.