Require Import Pam.Functions.MinClass.
Require Import Pam.Functions.Sequence.
Require Import Pam.Functions.Palindrome.
Require Import Pam.Functions.WordCheck.

(* The following imports are useful for extracting Haskell code. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction Language Haskell.
Extraction "PalindromeGenerated.hs" palindrome.
