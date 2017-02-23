Require Import Pam.BoolExtensions.
Require Import Pam.Functions.MinClass.
Require Import Pam.Functions.Sequence.
Require Import Pam.Functions.Palindrome.
Require Import Pam.Functions.WordCheck.
Require Import Pam.Functions.Levenshtein.

(* The following imports are useful for extracting Haskell code. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction Language Haskell.
Extraction "PamGenerated.hs" bool_to_nat palindrome wordcheck minclass sequence consecutive levenshtein_distance.
