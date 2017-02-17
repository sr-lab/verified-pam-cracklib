Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Import ListNotations.

(* The following imports are useful for extracting Haskell code *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Require Import Coq.Program.Basics.

Set Implicit Arguments.

(* I am defining strings as lists of ascii. There's probably a better way,
   but I couldn't find a pre-defined boolean equality for lists.
   TODO: investigate what is the better way to compare lists; can we use an Eq class,
   like in Haskell? *)
Fixpoint la_eq (s1: list ascii) (s2: list ascii) : bool :=
  match s1,s2 with
  | [],[] => true
  | x::xs,y::ys => andb
    (beq_nat (nat_of_ascii x) (nat_of_ascii y)) (la_eq xs ys)
  | _,_ => false
  end.


(* Definition by specification *)
Definition palindrome (s: list ascii) : bool :=
  la_eq (List.rev s) s.



(* In the near future, we can define a more efficient definition and
   PROVE that it is the same as this one. *)

(*
Fixpoint pal_aux (s: list ascii) (l: nat) (r: nat) : bool :=
  if (beq_nat l r) then true
  else andb (beq_nat (nat_of_ascii (nth l s " "%char)) (nat_of_ascii (nth r s " "%char))) (pal_aux s (l+1) (pred r)).

Definition palindrome2 (s: list ascii) : bool := pal_aux s 0 (length s).
 *)



(* Some examples that illustrate the function in use *)
Example ex1: (palindrome []) = true.
Proof. auto. Qed.

Example ex2: palindrome("a"%char :: "x"%char :: []) = false.
Proof. auto. Qed.
(* Or:
Proof. unfold palindrome. unfold rev. simpl. reflexivity. Qed.
 *)

Example ex3: palindrome("a"%char :: "b"%char :: "b"%char :: "a"%char :: []) = true.
Proof. auto. Qed.

(* This is probably better placed in the Interface file, but I'll keep it here
   for now. *)
Definition boolToNat (b : bool) : nat :=
  match b with
    | true => 1
    | false => 0
  end.


Extraction Language Haskell.
Extraction "PalindromeGenerated.hs" boolToNat palindrome.
