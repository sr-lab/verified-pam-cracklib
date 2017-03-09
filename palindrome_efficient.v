Require Import Coq.Init.Peano.
Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

(* Stand-in function. Remove. *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(* Stand-in function. Remove. *)
Definition beq_ascii (a b : option ascii) :=
  match a, b with
    | None, None => true
    | Some a', Some b' => (beq_nat (nat_of_ascii a') (nat_of_ascii b'))
    | _, _ => false
  end.

(* The recursive portion of the efficient palindrome function. *)
Fixpoint palindrome_efficient_r (s : string) (x y : nat) : bool :=
  if ble_nat y x then
    true (* This is included only for efficiency. *)
  else
    match y with
      | S y' => (beq_ascii (get x s) (get y' s)) 
        && (palindrome_efficient_r s (x + 1) y')
      | O => true
    end.

(* A more efficient implementation of the palindrome function. *)
Definition palindrome_efficient (s : string) : bool :=
  palindrome_efficient_r s 0 (length s).
