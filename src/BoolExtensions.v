(* Converts the boolean value true to the natural number 1, false to 0. *)
Fixpoint bool_to_nat (b : bool) : nat :=
  match b with
  | true => 1
  | false => 0
  end.