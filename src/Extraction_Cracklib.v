Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.

(* Import functions from framework. *)
Require Import Hapsl.Bool.Bool.
Require Import Hapsl.String.Distance.
Require Import Hapsl.String.Search.
Require Import Hapsl.String.Sequence.
Require Import Hapsl.String.Palindrome.

(* The following imports are useful for extracting Haskell code. *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Require Import Checkers.

Extraction Language Haskell.
Extraction "PamGenerated.hs" pwd_quality_policy.
