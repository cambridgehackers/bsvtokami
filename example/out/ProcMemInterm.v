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
    Let pc := mkReg (instancePrefix--"pc") ($0)%bk.
    Let rf := mkProcRegs (instancePrefix--"rf").
    Let sb := mkScoreboard (instancePrefix--"sb").
    Let e2wFifo := mkFIFO (instancePrefix--"e2wFifo").
    Let decexec := mkDecExec (instancePrefix--"decexec") (pgm)%bk (dec)%bk (exec)%bk (sb)%bk (e2wFifo)%bk (rf)%bk (mem)%bk (toHost)%bk.
    Let writeback := mkPipelinedWriteback (instancePrefix--"writeback") (e2wFifo)%bk (sb)%bk (rf)%bk.
    Local Open Scope kami_expr.

    Definition mkProcIntermModule: Mod :=
         (BKMODULE {
        (BKMod (Reg'mod pc :: nil))
    with (BKMod (ProcRegs'mod rf :: nil))
    with (BKMod (Scoreboard'mod sb :: nil))
    with (BKMod (FIFO'mod e2wFifo :: nil))
    with (BKMod (Empty'mod decexec :: nil))
    with (BKMod (Empty'mod writeback :: nil))
    }). (* mkProcInterm *)

(* Module mkProcInterm type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkProcInterm := Build_Empty mkProcIntermModule%kami.
    End Section'mkProcInterm.
End module'mkProcInterm.

Definition mkProcInterm := module'mkProcInterm.mkProcInterm.
Hint Unfold mkProcInterm : ModuleDefs.
Hint Unfold module'mkProcInterm.mkProcInterm : ModuleDefs.
Hint Unfold module'mkProcInterm.mkProcIntermModule : ModuleDefs.

