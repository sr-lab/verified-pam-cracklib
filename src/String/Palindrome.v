Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Require Import Hapsl.Ascii.Equality.
Require Import Hapsl.String.Equality.
Require Import Hapsl.String.Transform.

Import AsciiEqualityNotations.
Import StringEqualityNotations.

(* Returns true if a string is a palindrome, otherwise returns false. *)
Definition palindrome (s : string) : bool :=
  s ==_s (string_reverse s).

(* Prove that palindrome behaves correctly. *)
Theorem palindrome_correct : forall (s : string),
  s = string_reverse s -> Is_true (palindrome s).
Proof.
  intros.
  unfold palindrome.
  rewrite <- H.
  rewrite -> beq_string_reflexive.
  reflexivity.
Qed.

(* The recursive portion of the efficient palindrome function. *)
Fixpoint palindrome_efficient_recursive (s : string) (x y : nat) : bool :=
  if Nat.leb y x then
    true (* This is included only for efficiency. *)
  else
    match y with
      | S y' => (get x s) ?==_a (get y' s)
        && (palindrome_efficient_recursive s (x + 1) y')
      | O => true
    end.

(* A more efficient implementation of the palindrome function. *)
Definition palindrome_efficient (s : string) : bool :=
  palindrome_efficient_recursive s 0 (length s).
