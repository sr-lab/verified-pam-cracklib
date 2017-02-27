Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Pamba.Bool.Bool.
Require Import Pamba.Ascii.Equality.

Import AsciiEqualityNotations.

(* The Levenshtein indicator function that will return 0 if the character at 
   each given position is each given string is equal, otherwise returns 1. *)
Definition indicator (a b : string) (i j : nat) : nat :=
  nat_of_bool (negb ((get (i - 1) a) ?==_a (get (j - 1) b))).

(* The Levenshtein distance function. Returns the number of insertions, deletions
  and substitutions required to go from one string to another. *)
Fixpoint levenshtein (a b : string) (i j n : nat) : nat :=
  match i, j, n with
    | O, _, _ | _, O, _ | _, _, O => max i j
    | S i', S j', S n' => min 
      ((levenshtein a b i' j n') + 1)
      (min 
        ((levenshtein a b i j' n') + 1)
        ((levenshtein a b i' j' n') + (indicator a b i j)))
  end.

(* Calculates the Levenshtein distance betweem two strings. *)  
Definition levenshtein_distance (a b : string) : nat :=
  let i := length a in
    let j := length b in
      let n := max i j in
        levenshtein a b i j n.
