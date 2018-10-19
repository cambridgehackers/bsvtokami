Require Import Bool String List Arith.
Require Import Omega.
Require Import micromega.Lia.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Vector#(len, element_type) *)
Record Vector := {
    Vector'modules: Modules;
}.

Hint Unfold Vector'modules : ModuleDefs.

