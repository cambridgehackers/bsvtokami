Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import RegFile.
Require Import ProcMemSpec.
Require Import PipelinedProc.
Require Import ProcDecExec.
Module module'mkProcInterm.
    Section Section'mkProcInterm.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable mem: Memory.
    Variable toHost: ToHost.
        (* method bindings *)
    Let pc : string := instancePrefix--"pc".
    Let (* action binding *) rf := mkProcRegs (instancePrefix--"rf").
    Let (* action binding *) sb := mkScoreboard (instancePrefix--"sb").
    Let e2wFifo_reg : string := instancePrefix--"e2wFifo_reg".
    Let e2wFifo_valid : string := instancePrefix--"e2wFifo_valid".
    Let (* action binding *) decexec := mkDecExec (instancePrefix--"decexec") (pgm)%bk (dec)%bk (exec)%bk (e2wFifo_reg_v)%bk (e2wFifo_valid_v)%bk (rf)%bk (mem)%bk (toHost)%bk.
    Local Open Scope kami_expr.

    Definition mkProcIntermModule: Mod :=
         (BKMODULE {
        Register pc : Bit PgmSz <- $ (* int *) 0
    with (BKMod (ProcRegs'mod rf :: nil))
    with (BKMod (Scoreboard'mod sb :: nil))
    with Register e2wFifo_reg : E2W <- Default
    with Register e2wFifo_valid : Bool <- ($$false)%kami_expr
    with (BKMod (Empty'mod decexec :: nil))
    }). (* mkProcInterm *)

    Hint Unfold mkProcIntermModule : ModuleDefs.
(* Module mkProcInterm type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkProcInterm := Build_Empty mkProcIntermModule.
    Hint Unfold mkProcInterm : ModuleDefs.
    Hint Unfold mkProcIntermModule : ModuleDefs.

    End Section'mkProcInterm.
End module'mkProcInterm.

Definition mkProcInterm := module'mkProcInterm.mkProcInterm.
Hint Unfold mkProcInterm : ModuleDefs.
Hint Unfold module'mkProcInterm.mkProcInterm : ModuleDefs.
Hint Unfold module'mkProcInterm.mkProcIntermModule : ModuleDefs.

