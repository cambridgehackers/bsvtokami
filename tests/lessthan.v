Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition bitlt (x : nat) (y: nat): bool := (Nat.ltb x y).
Definition test_lt (a: (word 32)) (b: (word 32)): bool := 
    (bitlt #a #b).

