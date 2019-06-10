Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface RegFile#(index_t, data_t) *)
Record RegFile := {
    RegFile'mod: Mod;
    RegFile'upd : string;
    RegFile'sub : string;
}.

Hint Unfold RegFile'mod : ModuleDefs.
Hint Unfold RegFile'upd : ModuleDefs.
Hint Unfold RegFile'sub : ModuleDefs.

