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
    Let pc := mkReg (instancePrefix--"pc") (natToWord PgmSz 0)%bk.
    Let pc_read : string := (Reg'_read pc).
    Let pc_write : string := (Reg'_write pc).
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
    Local Open Scope kami_expr.

    Definition mkDecExecModule: Mod :=
         (BKMODULE {
        (BKMod (Reg'mod pc :: nil))
    with Rule instancePrefix--"decexecArith" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call call12 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call11 : Bool <-  decisOp ((#call12) : Bit InstrSz) (($$opArith) : OpK) ;
       Call call15 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call call14 : Bit RegFileSz <-  decgetSrc1 ((#call15) : Bit InstrSz) ;
       Call call13 : Bool <-  sbsearch1 ((#call14) : Bit RegFileSz) ;
       Call call18 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call call17 : Bit RegFileSz <-  decgetSrc2 ((#call18) : Bit InstrSz) ;
       Call call16 : Bool <-  sbsearch2 ((#call17) : Bit RegFileSz) ;

        Assert(((#call11 && (!#call13)) && (!#call16))) ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 ((#inst) : Bit InstrSz) ;
       Call dst : Bit RegFileSz (* varbinding *) <-  decgetDst ((#inst) : Bit InstrSz) ;
       Call arithOp : OpArithK (* varbinding *) <-  decgetArithOp ((#inst) : Bit InstrSz) ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
       Call val2 : Bit DataSz (* varbinding *) <-  rfread2 ((#src2) : Bit RegFileSz) ;
       BKCall execVal : Bit DataSz (* varbinding *) <-  execexecArith ((#arithOp) : OpArithK) ((#val1) : Bit DataSz) ((#val2) : Bit DataSz) ;
               Call inserted : Void (* actionBinding *) <- sbinsert ((#dst) : Bit RegFileSz) ;
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               Call enq : Void (* actionBinding *) <- e2wFifoenq ((#e2w) : E2W) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule decexecArith *)
    with Rule instancePrefix--"decexecLd" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call call20 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call19 : Bool <-  decisOp ((#call20) : Bit InstrSz) (($$opLd) : OpK) ;
       Call call23 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call call22 : Bit RegFileSz <-  decgetDst ((#call23) : Bit InstrSz) ;
       Call call21 : Bool <-  sbsearch1 ((#call22) : Bit RegFileSz) ;

        Assert((#call19 && (!#call21))) ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call dst : Bit RegFileSz (* varbinding *) <-  decgetDst ((#inst) : Bit InstrSz) ;
       Call addr : Bit AddrSz (* varbinding *) <-  decgetAddr ((#inst) : Bit InstrSz) ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (natToWord 1 1))  }%kami_expr ;
               Call ldVal : Bit DataSz (* actionBinding *) <- memdoMem ((#memrq) : MemRq) ;
               Call inserted : Void (* actionBinding *) <- sbinsert ((#dst) : Bit RegFileSz) ;
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#ldVal)  }%kami_expr ;
               Call enq : Void (* actionBinding *) <- e2wFifoenq ((#e2w) : E2W) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule decexecLd *)
    with Rule instancePrefix--"decexecSt" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call call25 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call24 : Bool <-  decisOp ((#call25) : Bit InstrSz) (($$opSt) : OpK) ;

        Assert(#call24) ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call addr : Bit AddrSz (* varbinding *) <-  decgetAddr ((#inst) : Bit InstrSz) ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (natToWord 1 0))  }%kami_expr ;
               Call unused : Bit DataSz (* actionBinding *) <- memdoMem ((#memrq) : MemRq) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule decexecSt *)
    with Rule instancePrefix--"decexecToHost" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call call27 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call26 : Bool <-  decisOp ((#call27) : Bit InstrSz) (($$opTh) : OpK) ;
       Call call30 : Bit InstrSz <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call call29 : Bit RegFileSz <-  decgetSrc1 ((#call30) : Bit InstrSz) ;
       Call call28 : Bool <-  sbsearch1 ((#call29) : Bit RegFileSz) ;

        Assert((#call26 && (!#call28))) ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
               Call unused : Void (* actionBinding *) <- toHosttoHost ((#val1) : Bit DataSz) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule decexecToHost *)
    }). (* mkDecExec *)

    Hint Unfold mkDecExecModule : ModuleDefs.

(* Module mkDecExec type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> Scoreboard -> FIFO#(E2W) -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkDecExec := Build_Empty mkDecExecModule%kami.
    Hint Unfold mkDecExec : ModuleDefs.
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
    Let d2eFifo := mkFIFO D2E (instancePrefix--"d2eFifo").
    Let e2wFifo := mkFIFO E2W (instancePrefix--"e2wFifo").
    Let mem := mkMemory (instancePrefix--"mem").
    Let rf := mkProcRegs (instancePrefix--"rf").
    Let sb := mkScoreboard (instancePrefix--"sb").
    Let decoder := mkPipelinedDecoder (instancePrefix--"decoder") (pgm)%bk (dec)%bk (d2eFifo)%bk.
    Let executer := mkPipelinedExecuter (instancePrefix--"executer") (d2eFifo)%bk (e2wFifo)%bk (sb)%bk (exec)%bk (rf)%bk (mem)%bk (toHost)%bk.
    Local Open Scope kami_expr.

    Definition mkDecExecSepModule: Mod :=
         (BKMODULE {
        (BKMod (FIFO'mod d2eFifo :: nil))
    with (BKMod (FIFO'mod e2wFifo :: nil))
    with (BKMod (Memory'mod mem :: nil))
    with (BKMod (ProcRegs'mod rf :: nil))
    with (BKMod (Scoreboard'mod sb :: nil))
    with (BKMod (Empty'mod decoder :: nil))
    with (BKMod (Empty'mod executer :: nil))
    }). (* mkDecExecSep *)

(* Module mkDecExecSep type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkDecExecSep := Build_Empty mkDecExecSepModule%kami.
    End Section'mkDecExecSep.
End module'mkDecExecSep.

Definition mkDecExecSep := module'mkDecExecSep.mkDecExecSep.
Hint Unfold mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSepModule : ModuleDefs.

