Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Require Import Hapsl.Bool.Bool.
Require Import Hapsl.Ascii.Equality.

Import AsciiEqualityNotations.

(* Calculates the Hamming distance between two strings. *)
Fixpoint hamming_distance (a b : string) : option nat :=
  match a, b with
    | EmptyString, EmptyString => Some 0
    | String ca a', String cb b' =>
      match hamming_distance a' b' with
        | None => None
        | Some n => Some ((nat_of_bool (negb (ca ==_a cb))) + n)
      end
    | _, _ => None
  end.

(* TODO: Prove lemma - Hamming distance is undefined for strings with differing 
   lengths. *)
Lemma hamming_distance_undefined_for_different_lengths : forall (a b : string),
  length a <> length b <-> hamming_distance a b = None.
Proof.
  Admitted.
  

(* TODO: Prove lemma - Hamming distance is defined for strings with the same 
   length. *)
Lemma hamming_distance_defined_for_same_length : forall (a b : string),
  length a = length b -> hamming_distance a b <> None.
Proof.
  Admitted.

(* Hamming distance is 0 for identical strings. *)
Lemma hamming_distance_zero_for_identical : forall (s: string),
  hamming_distance s s = Some 0.
Proof.
  induction s.
    - auto.
    - unfold hamming_distance.
      rewrite beq_ascii_reflexive.
      simpl.
      fold hamming_distance.
      rewrite IHs.
      reflexivity.
Qed.

(* TODO: Prove lemma - Hamming distance is at most string length. *)
Lemma hamming_distance_at_most_string_length : forall (a b : string),
  True.
  (* TODO: Option nat conversion. *)
  (* length a = length b -> hamming_distance a b <= length a. *)
Proof.
  Admitted.

(* The Levenshtein indicator function that will return 0 if the character at 
   each given position is each given string is equal, otherwise returns 1. *)
Definition indicator (a b : string) (i j : nat) : nat :=
  nat_of_bool (negb ((get (i - 1) a) ?==_a (get (j - 1) b))).

(* The Levenshtein distance function. Returns the number of insertions, 
   deletions and substitutions required to go from one string to another. *)
Fixpoint levenshtein (a b : string) (i j n : nat) : nat :=
  match i, j, n with
    | O, _, _ | _, O, _ | _, _, O => max i j
    | S i', S j', S n' => min 
      ((levenshtein a b i' j n') + 1)
      (min 
        ((levenshtein a b i j' n') + 1)
        ((levenshtein a b i' j' n') + (indicator a b i j)))
  end.

(* Calculates the Levenshtein distance between two strings. *)
Definition levenshtein_distance (a b : string) : nat :=
  let i := length a in
    let j := length b in
      let n := max i j in
        levenshtein a b i j n.

(* Returns the length difference between two strings. *)
Fixpoint string_length_diff (a b : string) : nat :=
  match a, b with
    | EmptyString, EmptyString => 0
    | _, EmptyString => length a
    | EmptyString, _ => length b
    | String ca a', String cb b' => string_length_diff a' b'
  end.

(* TODO: Prove lemma - It is always at least the difference of the sizes of the 
   two strings. *)
Lemma levenshtein_distance_at_least_length_diff : forall (a b : string),    
  levenshtein_distance a b >= string_length_diff a b.
Proof.
  Admitted.

(* TODO: Prove lemma - It is zero if and only if the strings are equal. *)
Lemma levenshtein_distance_zero_for_equal_strings : forall (a b : string),
  a = b <-> levenshtein_distance a b = 0.
Proof.
  Admitted.

(* TODO: Prove lemma - If the strings are the same size, the Hamming distance is
   an upper bound on the Levenshtein distance. *)
Lemma levenshtein_distance_same_length_leq_hamming : forall (a b : string),
  True.
  (* TODO: Option nat conversion. *)
  (* length a = length b -> levenshtein_distance a b <= hamming_distance a b. *)
Proof.
  Admitted.

(* TODO: Prove lemma - It is at most the length of the longer string. *)
Lemma levenshtein_distance_leq_longer_string_length : forall (a b : string),
  levenshtein_distance a b <= max (length a) (length b).
Proof.
  Admitted.

(* TODO: Prove lemma - The Levenshtein distance between two strings is no 
   greater than the sum of their Levenshtein distances from a third string 
   (triangle inequality). *)
Lemma levenshtein_distance_triangle_inequality : forall (a b c : string),
  levenshtein_distance a b <= (levenshtein_distance a c) 
    + (levenshtein_distance b c).
Proof.
  Admitted.
