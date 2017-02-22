Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Definition bool_to_nat (b : bool) : nat :=
  match b with
    | true => 1
    | false => 0
  end.

Definition unpack_option_ascii (a : option ascii) : ascii :=
  match a with
    | None => zero
    | Some a => a
  end.

Definition indicator (a b : string) (i j : nat) : nat :=
  bool_to_nat (negb (beq_nat
    (nat_of_ascii (unpack_option_ascii (get (i - 1) a)))
    (nat_of_ascii (unpack_option_ascii (get (j - 1) b))))).

Fixpoint levenshtein (a b : string) (i j n : nat) : nat :=
  match i, j, n with
    | O, _, _ | _, O, _ | _, _, O => max i j
    | S i', S j', S n' => 
      min 
        ((levenshtein a b i' j n') + 1)
        (min 
          ((levenshtein a b i j' n') + 1)
          ((levenshtein a b i' j' n') + (indicator a b i j)))
  end.

Fixpoint levenshtein_distance (a b : string) : nat :=
  let i := length a in
    let j := length b in
      let n := max i j in
        levenshtein a b i j n.

Compute levenshtein_distance "joaoferreira" "juao".