Require Import Bool String List Arith.
Require Import Omega.
Require Import micromega.Lia.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import RegFile.
Require Import ProcMemSpec.
Require Import PipelinedProc.
Module module'mkDecExec.
    Section Section'mkDecExec.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable sb: Scoreboard.
    Variable e2wFifo: FIFO.
    Variable rf: ProcRegs.
    Variable mem: Memory.
    Variable toHost: ToHost.
        (* method bindings *)
    (* method binding *) Let pc := mkReg (Bit PgmSz) (instancePrefix--"pc") ($0)%bk.
    (* method binding *) Let pc_read : string := (Reg'_read pc).
    (* method binding *) Let pc_write : string := (Reg'_write pc).
    (* instance methods *)
    Let decgetAddr : string := (Decoder'getAddr dec).
    Let decgetArithOp : string := (Decoder'getArithOp dec).
    Let decgetDst : string := (Decoder'getDst dec).
    Let decgetSrc1 : string := (Decoder'getSrc1 dec).
    Let decgetSrc2 : string := (Decoder'getSrc2 dec).
    Let decisOp : string := (Decoder'isOp dec).
    Let e2wFifoenq : string := (FIFO'enq e2wFifo).
    Let execexecArith : string := (Executer'execArith exec).
    Let memdoMem : string := (Memory'doMem mem).
    Let pgmsub : string := (RegFile'sub pgm).
    Let rfread1 : string := (ProcRegs'read1 rf).
    Let rfread2 : string := (ProcRegs'read2 rf).
    Let sbinsert : string := (Scoreboard'insert sb).
    Let sbsearch1 : string := (Scoreboard'search1 sb).
    Let sbsearch2 : string := (Scoreboard'search2 sb).
    Let toHosttoHost : string := (ToHost'toHost toHost).
    Definition mkDecExecModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules pc :: nil))
    with Rule instancePrefix--"decexecArith" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM call12 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call11 : Bool <-  decisOp (#call12 : Bit InstrSz) ($$opArith : OpK);
       CallM call15 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call14 : Bit RegFileSz <-  decgetSrc1 (#call15 : Bit InstrSz);
       CallM call13 : Bool <-  sbsearch1 (#call14 : Bit RegFileSz);
       CallM call18 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call17 : Bit RegFileSz <-  decgetSrc2 (#call18 : Bit InstrSz);
       CallM call16 : Bool <-  sbsearch2 (#call17 : Bit RegFileSz);

        Assert(((#call11 && (!#call13)) && (!#call16)));
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 (#inst : Bit InstrSz);
       CallM dst : Bit RegFileSz (* varbinding *) <-  decgetDst (#inst : Bit InstrSz);
       CallM arithOp : OpArithK (* varbinding *) <-  decgetArithOp (#inst : Bit InstrSz);
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
       CallM val2 : Bit DataSz (* varbinding *) <-  rfread2 (#src2 : Bit RegFileSz);
       CallM execVal : Bit DataSz (* varbinding *) <-  execexecArith (#arithOp : OpArithK) (#val1 : Bit DataSz) (#val2 : Bit DataSz);
               CallM inserted : Void (* actionBinding *) <- sbinsert (#dst : Bit RegFileSz);
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst); "val" ::= (#execVal)  }%kami_expr;
               CallM enq : Void (* actionBinding *) <- e2wFifoenq (#e2w : E2W);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule decexecArith *)
    with Rule instancePrefix--"decexecLd" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM call20 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call19 : Bool <-  decisOp (#call20 : Bit InstrSz) ($$opLd : OpK);
       CallM call23 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call22 : Bit RegFileSz <-  decgetDst (#call23 : Bit InstrSz);
       CallM call21 : Bool <-  sbsearch1 (#call22 : Bit RegFileSz);

        Assert((#call19 && (!#call21)));
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM dst : Bit RegFileSz (* varbinding *) <-  decgetDst (#inst : Bit InstrSz);
       CallM addr : Bit AddrSz (* varbinding *) <-  decgetAddr (#inst : Bit InstrSz);
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr); "data" ::= (#val1); "isLoad" ::= ($$(natToWord 1 1))  }%kami_expr;
               CallM ldVal : Bit DataSz (* actionBinding *) <- memdoMem (#memrq : MemRq);
               CallM inserted : Void (* actionBinding *) <- sbinsert (#dst : Bit RegFileSz);
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst); "val" ::= (#ldVal)  }%kami_expr;
               CallM enq : Void (* actionBinding *) <- e2wFifoenq (#e2w : E2W);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule decexecLd *)
    with Rule instancePrefix--"decexecSt" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM call25 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call24 : Bool <-  decisOp (#call25 : Bit InstrSz) ($$opSt : OpK);

        Assert(#call24);
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM addr : Bit AddrSz (* varbinding *) <-  decgetAddr (#inst : Bit InstrSz);
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr); "data" ::= (#val1); "isLoad" ::= ($$(natToWord 1 0))  }%kami_expr;
               CallM unused : Bit DataSz (* actionBinding *) <- memdoMem (#memrq : MemRq);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule decexecSt *)
    with Rule instancePrefix--"decexecToHost" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM call27 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call26 : Bool <-  decisOp (#call27 : Bit InstrSz) ($$opTh : OpK);
       CallM call30 : Bit InstrSz <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call29 : Bit RegFileSz <-  decgetSrc1 (#call30 : Bit InstrSz);
       CallM call28 : Bool <-  sbsearch1 (#call29 : Bit RegFileSz);

        Assert((#call26 && (!#call28)));
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
               CallM unused : Void (* actionBinding *) <- toHosttoHost (#val1 : Bit DataSz);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule decexecToHost *)
    }). (* mkDecExec *)

(* Module mkDecExec type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> Scoreboard -> FIFO#(E2W) -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkDecExec := Build_Empty mkDecExecModule%kami.
    End Section'mkDecExec.
End module'mkDecExec.

Definition mkDecExec := module'mkDecExec.mkDecExec.
Hint Unfold mkDecExec : ModuleDefs.
Hint Unfold module'mkDecExec.mkDecExec : ModuleDefs.
Hint Unfold module'mkDecExec.mkDecExecModule : ModuleDefs.

Module module'mkDecExecSep.
    Section Section'mkDecExecSep.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable toHost: ToHost.
        (* method bindings *)
    (* method binding *) Let d2eFifo := mkFIFO D2E (instancePrefix--"d2eFifo").
    (* method binding *) Let e2wFifo := mkFIFO E2W (instancePrefix--"e2wFifo").
    (* method binding *) Let mem := mkMemory (instancePrefix--"mem").
    (* method binding *) Let rf := mkProcRegs (instancePrefix--"rf").
    (* method binding *) Let sb := mkScoreboard (instancePrefix--"sb").
    (* method binding *) Let decoder := mkPipelinedDecoder (instancePrefix--"decoder") (pgm)%bk (dec)%bk (d2eFifo)%bk.
    (* method binding *) Let executer := mkPipelinedExecuter (instancePrefix--"executer") (d2eFifo)%bk (e2wFifo)%bk (sb)%bk (exec)%bk (rf)%bk (mem)%bk (toHost)%bk.
    Definition mkDecExecSepModule: Modules :=
         (BKMODULE {
        (BKMod (FIFO'modules d2eFifo :: nil))
    with (BKMod (FIFO'modules e2wFifo :: nil))
    with (BKMod (Memory'modules mem :: nil))
    with (BKMod (ProcRegs'modules rf :: nil))
    with (BKMod (Scoreboard'modules sb :: nil))
    with (BKMod (Empty'modules decoder :: nil))
    with (BKMod (Empty'modules executer :: nil))
    }). (* mkDecExecSep *)

(* Module mkDecExecSep type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkDecExecSep := Build_Empty mkDecExecSepModule%kami.
    End Section'mkDecExecSep.
End module'mkDecExecSep.

Definition mkDecExecSep := module'mkDecExecSep.mkDecExecSep.
Hint Unfold mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSepModule : ModuleDefs.

