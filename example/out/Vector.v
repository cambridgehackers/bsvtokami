Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Vector#(len, element_type) *)
Record Vector := {
    Vector'mod: Mod;
}.

Hint Unfold Vector'mod : ModuleDefs.

