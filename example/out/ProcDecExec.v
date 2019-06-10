Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFOF.
Require Import RegFile.
Require Import ProcMemSpec.
Require Import PipelinedProc.
Require Import Vector.
(* * interface NoMethods *)
Record NoMethods := {
    NoMethods'mod: Mod;
}.

Hint Unfold NoMethods'mod : ModuleDefs.

Module module'mkDecExecSep.
    Section Section'mkDecExecSep.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable mem: Memory.
    Variable rf: Reg.
