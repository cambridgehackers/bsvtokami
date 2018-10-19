Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import FIFO.
Require Import ProcMemSpec.
Require Import RegFile.
(* * interface ProcRegs *)
Record ProcRegs := {
    ProcRegs'mod: Mod;
    ProcRegs'read1 : string;
    ProcRegs'read2 : string;
    ProcRegs'write : string;
}.

Hint Unfold ProcRegs'mod : ModuleDefs.
Hint Unfold ProcRegs'read1 : ModuleDefs.
Hint Unfold ProcRegs'read2 : ModuleDefs.
Hint Unfold ProcRegs'write : ModuleDefs.

Module module'mkProcRegs.
    Section Section'mkProcRegs.
    Variable instancePrefix: string.
    (* let bindings *)
    Definition write'paramsT :=  ( STRUCT { "_1" :: (Bit RegFileSz) ; "_2" :: (Bit DataSz) })%kami_struct.
        (* method bindings *)
    Let rf := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"rf").
    (* instance methods *)
    Let rfsub : string := (RegFile'sub rf).
    Let rfupd : string := (RegFile'upd rf).
    Local Open Scope kami_expr.

    Definition mkProcRegsModule: Mod :=
         (BKMODULE {
        (BKMod (RegFile'mod rf :: nil))
    with Method (instancePrefix--"read1") (r1 : (Bit RegFileSz)) : Bit DataSz :=
    (
Call val : Bit DataSz (* varbinding *) <-  rfsub ((#r1) : Bit RegFileSz) ;
        Ret #val    )

    with Method (instancePrefix--"read2") (r2 : (Bit RegFileSz)) : Bit DataSz :=
    (
Call val : Bit DataSz (* varbinding *) <-  rfsub ((#r2) : Bit RegFileSz) ;
        Ret #val    )

    with Method (instancePrefix--"write") ( params : write'paramsT )  : Void :=
    (
        LET r : (Bit RegFileSz) <- #params @% "_1" ;
        LET val : (Bit DataSz) <- #params @% "_2" ;
        BKCall written : Void (* actionBinding *) <- rfupd ((#r) : Bit RegFileSz) ((#val) : Bit DataSz) ;
        Retv    )

    }). (* mkProcRegs *)

(* Module mkProcRegs type Module#(ProcRegs) return type ProcRegs *)
    Definition mkProcRegs := Build_ProcRegs mkProcRegsModule%kami (instancePrefix--"read1") (instancePrefix--"read2") (instancePrefix--"write").
    End Section'mkProcRegs.
End module'mkProcRegs.

Definition mkProcRegs := module'mkProcRegs.mkProcRegs.
Hint Unfold mkProcRegs : ModuleDefs.
Hint Unfold module'mkProcRegs.mkProcRegs : ModuleDefs.
Hint Unfold module'mkProcRegs.mkProcRegsModule : ModuleDefs.

Definition D2E := (STRUCT {
    "addr" :: Bit AddrSz;
    "arithOp" :: OpArithK;
    "dst" :: Bit RegFileSz;
    "op" :: OpK;
    "pc" :: Bit PgmSz;
    "src1" :: Bit RegFileSz;
    "src2" :: Bit RegFileSz}).

Module module'mkPipelinedDecoder.
    Section Section'mkPipelinedDecoder.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable d2eFifo: FIFO.
        (* method bindings *)
    Let pc := mkReg (instancePrefix--"pc") (natToWord PgmSz 0)%bk.
    Let pc_read : string := (Reg'_read pc).
    Let pc_write : string := (Reg'_write pc).
    (* instance methods *)
    Let d2eFifoenq : string := (FIFO'enq d2eFifo).
    Let decgetAddr : string := (Decoder'getAddr dec).
    Let decgetArithOp : string := (Decoder'getArithOp dec).
    Let decgetDst : string := (Decoder'getDst dec).
    Let decgetOp : string := (Decoder'getOp dec).
    Let decgetSrc1 : string := (Decoder'getSrc1 dec).
    Let decgetSrc2 : string := (Decoder'getSrc2 dec).
    Let pgmsub : string := (RegFile'sub pgm).
    Local Open Scope kami_expr.

    Definition mkPipelinedDecoderModule: Mod :=
         (BKMODULE {
        (BKMod (Reg'mod pc :: nil))
    with Rule instancePrefix--"decode" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       Call op : OpK (* varbinding *) <-  decgetOp ((#inst) : Bit InstrSz) ;
       Call arithOp : OpArithK (* varbinding *) <-  decgetArithOp ((#inst) : Bit InstrSz) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 ((#inst) : Bit InstrSz) ;
       Call dst : Bit RegFileSz (* varbinding *) <-  decgetDst ((#inst) : Bit InstrSz) ;
       Call addr : Bit AddrSz (* varbinding *) <-  decgetAddr ((#inst) : Bit InstrSz) ;
               LET decoded : D2E <- STRUCT { "addr" ::= (#addr) ; "arithOp" ::= (#arithOp) ; "dst" ::= (#dst) ; "op" ::= (#op) ; "pc" ::= (#pc_v) ; "src1" ::= (#src1) ; "src2" ::= (#src2)  }%kami_expr ;
               Call enq : Void (* actionBinding *) <- d2eFifoenq ((#decoded) : D2E) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule decode *)
    }). (* mkPipelinedDecoder *)

(* Module mkPipelinedDecoder type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> FIFO#(D2E) -> Module#(Empty) return type Decoder *)
    Definition mkPipelinedDecoder := Build_Empty mkPipelinedDecoderModule%kami.
    End Section'mkPipelinedDecoder.
End module'mkPipelinedDecoder.

Definition mkPipelinedDecoder := module'mkPipelinedDecoder.mkPipelinedDecoder.
Hint Unfold mkPipelinedDecoder : ModuleDefs.
Hint Unfold module'mkPipelinedDecoder.mkPipelinedDecoder : ModuleDefs.
Hint Unfold module'mkPipelinedDecoder.mkPipelinedDecoderModule : ModuleDefs.

(* * interface Scoreboard *)
Record Scoreboard := {
    Scoreboard'mod: Mod;
    Scoreboard'search1 : string;
    Scoreboard'search2 : string;
    Scoreboard'insert : string;
    Scoreboard'remove : string;
}.

Hint Unfold Scoreboard'mod : ModuleDefs.
Hint Unfold Scoreboard'search1 : ModuleDefs.
Hint Unfold Scoreboard'search2 : ModuleDefs.
Hint Unfold Scoreboard'insert : ModuleDefs.
Hint Unfold Scoreboard'remove : ModuleDefs.

Module module'mkScoreboard.
    Section Section'mkScoreboard.
    Variable instancePrefix: string.
        (* method bindings *)
    Let sbFlags := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"sbFlags").
    (* instance methods *)
    Let sbFlagssub : string := (RegFile'sub sbFlags).
    Let sbFlagsupd : string := (RegFile'upd sbFlags).
    Local Open Scope kami_expr.

    Definition mkScoreboardModule: Mod :=
         (BKMODULE {
        (BKMod (RegFile'mod sbFlags :: nil))
    with Method (instancePrefix--"search1") (sidx : (Bit RegFileSz)) : Bool :=
    (
Call flag : Bool (* varbinding *) <-  sbFlagssub ((#sidx) : Bit RegFileSz) ;
        Ret #flag    )

    with Method (instancePrefix--"search2") (sidx : (Bit RegFileSz)) : Bool :=
    (
Call flag : Bool (* varbinding *) <-  sbFlagssub ((#sidx) : Bit RegFileSz) ;
        Ret #flag    )

    with Method (instancePrefix--"insert") (nidx : (Bit RegFileSz)) : Void :=
    (
        BKCall unused : Void (* actionBinding *) <- sbFlagsupd ((#nidx) : Bit RegFileSz) ((($$true)%kami_expr) : Bool) ;
        Retv    )

    with Method (instancePrefix--"remove") (nidx : (Bit RegFileSz)) : Void :=
    (
        BKCall unused : Void (* actionBinding *) <- sbFlagsupd ((#nidx) : Bit RegFileSz) ((($$false)%kami_expr) : Bool) ;
        Retv    )

    }). (* mkScoreboard *)

(* Module mkScoreboard type Module#(Scoreboard) return type Scoreboard *)
    Definition mkScoreboard := Build_Scoreboard mkScoreboardModule%kami (instancePrefix--"insert") (instancePrefix--"remove") (instancePrefix--"search1") (instancePrefix--"search2").
    End Section'mkScoreboard.
End module'mkScoreboard.

Definition mkScoreboard := module'mkScoreboard.mkScoreboard.
Hint Unfold mkScoreboard : ModuleDefs.
Hint Unfold module'mkScoreboard.mkScoreboard : ModuleDefs.
Hint Unfold module'mkScoreboard.mkScoreboardModule : ModuleDefs.

Definition E2W := (STRUCT {
    "idx" :: Bit RegFileSz;
    "val" :: Bit DataSz}).

Module module'mkPipelinedExecuter.
    Section Section'mkPipelinedExecuter.
    Variable instancePrefix: string.
    Variable d2eFifo: FIFO.
    Variable e2wFifo: FIFO.
    Variable sb: Scoreboard.
    Variable exec: Executer.
    Variable rf: ProcRegs.
    Variable mem: Memory.
    Variable toHost: ToHost.
    (* instance methods *)
    Let d2eFifodeq : string := (FIFO'deq d2eFifo).
    Let d2eFifofirst : string := (FIFO'first d2eFifo).
    Let e2wFifoenq : string := (FIFO'enq e2wFifo).
    Let execexecArith : string := (Executer'execArith exec).
    Let memdoMem : string := (Memory'doMem mem).
    Let rfread1 : string := (ProcRegs'read1 rf).
    Let rfread2 : string := (ProcRegs'read2 rf).
    Let sbinsert : string := (Scoreboard'insert sb).
    Let sbsearch1 : string := (Scoreboard'search1 sb).
    Let sbsearch2 : string := (Scoreboard'search2 sb).
    Let toHosttoHost : string := (ToHost'toHost toHost).
    Local Open Scope kami_expr.

    Definition mkPipelinedExecuterModule: Mod :=
         (BKMODULE {
        Rule instancePrefix--"executeArith" :=
    (
       Call d2e : D2E (* varbinding *) <-  d2eFifofirst () ;
       Call call5 : Bool <-  sbsearch1 (((#d2e @% "src1")) : Bit RegFileSz) ;
       Call call6 : Bool <-  sbsearch2 (((#d2e @% "src2")) : Bit RegFileSz) ;

        Assert (((((#d2e @% "op") == #opArith) && (!#call5)) && (!#call6))) ;
               Call deq : Void (* actionBinding *) <- d2eFifodeq () ;
               LET src1 : Bit RegFileSz <- (#d2e @% "src1") ;
               LET src2 : Bit RegFileSz <- (#d2e @% "src2") ;
               LET dst : Bit RegFileSz <- (#d2e @% "dst") ;
               LET arithOp : OpArithK <- (#d2e @% "arithOp") ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
       Call val2 : Bit DataSz (* varbinding *) <-  rfread2 ((#src2) : Bit RegFileSz) ;
       BKCall execVal : Bit DataSz (* varbinding *) <-  execexecArith ((#arithOp) : OpArithK) ((#val1) : Bit DataSz) ((#val2) : Bit DataSz) ;
               Call upd : Void (* actionBinding *) <- sbinsert ((#dst) : Bit RegFileSz) ;
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               Call enq : Void (* actionBinding *) <- e2wFifoenq ((#e2w) : E2W) ;
        Retv ) (* rule executeArith *)
    with Rule instancePrefix--"executeLoad" :=
    (
       Call d2e : D2E (* varbinding *) <-  d2eFifofirst () ;
       Call call7 : Bool <-  sbsearch1 (((#d2e @% "src1")) : Bit RegFileSz) ;
       Call call8 : Bool <-  sbsearch2 (((#d2e @% "dst")) : Bit RegFileSz) ;

        Assert(((((#d2e @% "op") == $$opLd) && (!#call7)) && (!#call8))) ;
               Call deq : Void (* actionBinding *) <- d2eFifodeq () ;
               LET src1 : Bit RegFileSz <- (#d2e @% "src1") ;
               LET dst : Bit RegFileSz <- (#d2e @% "dst") ;
               LET addr : Bit AddrSz <- (#d2e @% "addr") ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr) ; "data" ::= ($$ (natToWord 32 0)) ; "isLoad" ::= ($$ (natToWord 1 1))  }%kami_expr ;
               Call ldVal : Bit DataSz (* actionBinding *) <- memdoMem ((#memrq) : MemRq) ;
               Call insert : Void (* actionBinding *) <- sbinsert ((#dst) : Bit RegFileSz) ;
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#ldVal)  }%kami_expr ;
               Call enq : Void (* actionBinding *) <- e2wFifoenq ((#e2w) : E2W) ;
        Retv ) (* rule executeLoad *)
    with Rule instancePrefix--"executeStore" :=
    (
       Call d2e : D2E (* varbinding *) <-  d2eFifofirst () ;
       Call call9 : Bool <-  sbsearch1 (((#d2e @% "src1")) : Bit RegFileSz) ;

        Assert((((#d2e @% "op") == $$opSt) && (!#call9))) ;
               Call deq : Void (* actionBinding *) <- d2eFifodeq () ;
               LET src1 : Bit RegFileSz <- (#d2e @% "src1") ;
               LET addr : Bit AddrSz <- (#d2e @% "addr") ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (natToWord 1 0))  }%kami_expr ;
               Call unused : Bit DataSz (* actionBinding *) <- memdoMem ((#memrq) : MemRq) ;
        Retv ) (* rule executeStore *)
    with Rule instancePrefix--"executeToHost" :=
    (
       Call d2e : D2E (* varbinding *) <-  d2eFifofirst () ;
       Call call10 : Bool <-  sbsearch1 (((#d2e @% "src1")) : Bit RegFileSz) ;

        Assert((((#d2e @% "op") == $$opTh) && (!#call10))) ;
               Call deq : Void (* actionBinding *) <- d2eFifodeq () ;
               LET src1 : Bit RegFileSz <- (#d2e @% "src1") ;
               LET addr : Bit AddrSz <- (#d2e @% "addr") ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfread1 ((#src1) : Bit RegFileSz) ;
               Call unused : Void (* actionBinding *) <- toHosttoHost ((#val1) : Bit DataSz) ;
        Retv ) (* rule executeToHost *)
    }). (* mkPipelinedExecuter *)

(* Module mkPipelinedExecuter type FIFO#(D2E) -> FIFO#(E2W) -> Scoreboard -> Executer -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type FIFO#(E2W) *)
    Definition mkPipelinedExecuter := Build_Empty mkPipelinedExecuterModule%kami.
    End Section'mkPipelinedExecuter.
End module'mkPipelinedExecuter.

Definition mkPipelinedExecuter := module'mkPipelinedExecuter.mkPipelinedExecuter.
Hint Unfold mkPipelinedExecuter : ModuleDefs.
Hint Unfold module'mkPipelinedExecuter.mkPipelinedExecuter : ModuleDefs.
Hint Unfold module'mkPipelinedExecuter.mkPipelinedExecuterModule : ModuleDefs.

Module module'mkPipelinedWriteback.
    Section Section'mkPipelinedWriteback.
    Variable instancePrefix: string.
    Variable e2wFifo: FIFO.
    Variable sb: Scoreboard.
    Variable rf: ProcRegs.
    (* instance methods *)
    Let e2wFifodeq : string := (FIFO'deq e2wFifo).
    Let e2wFifofirst : string := (FIFO'first e2wFifo).
    Let rfwrite : string := (ProcRegs'write rf).
    Let sbremove : string := (Scoreboard'remove sb).
    Local Open Scope kami_expr.

    Definition mkPipelinedWritebackModule: Mod :=
         (BKMODULE {
        Rule instancePrefix--"writeback" :=
    (
       Call e2w : E2W (* varbinding *) <-  e2wFifofirst () ;
               Call deq : Void (* actionBinding *) <- e2wFifodeq () ;
               LET idx : Bit RegFileSz <- (#e2w @% "idx") ;
               LET val : Bit DataSz <- (#e2w @% "val") ;
               Call written : Void (* actionBinding *) <- rfwrite ((#idx) : Bit RegFileSz) ((#val) : Bit DataSz) ;
               Call removed : Void (* actionBinding *) <- sbremove ((#idx) : Bit RegFileSz) ;
        Retv ) (* rule writeback *)
    }). (* mkPipelinedWriteback *)

(* Module mkPipelinedWriteback type FIFO#(E2W) -> Scoreboard -> ProcRegs -> Module#(Empty) return type Scoreboard *)
    Definition mkPipelinedWriteback := Build_Empty mkPipelinedWritebackModule%kami.
    End Section'mkPipelinedWriteback.
End module'mkPipelinedWriteback.

Definition mkPipelinedWriteback := module'mkPipelinedWriteback.mkPipelinedWriteback.
Hint Unfold mkPipelinedWriteback : ModuleDefs.
Hint Unfold module'mkPipelinedWriteback.mkPipelinedWriteback : ModuleDefs.
Hint Unfold module'mkPipelinedWriteback.mkPipelinedWritebackModule : ModuleDefs.

Module module'mkProcImpl.
    Section Section'mkProcImpl.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable toHost: ToHost.
        (* method bindings *)
    Let d2eFifo := mkFIFO (instancePrefix--"d2eFifo").
    Let e2wFifo := mkFIFO (instancePrefix--"e2wFifo").
    Let mem := mkMemory (instancePrefix--"mem").
    Let rf := mkProcRegs (instancePrefix--"rf").
    Let sb := mkScoreboard (instancePrefix--"sb").
    Let decoder := mkPipelinedDecoder (instancePrefix--"decoder") (pgm)%bk (dec)%bk (d2eFifo)%bk.
    Let executer := mkPipelinedExecuter (instancePrefix--"executer") (d2eFifo)%bk (e2wFifo)%bk (sb)%bk (exec)%bk (rf)%bk (mem)%bk (toHost)%bk.
    Let writeback := mkPipelinedWriteback (instancePrefix--"writeback") (e2wFifo)%bk (sb)%bk (rf)%bk.
    Local Open Scope kami_expr.

    Definition mkProcImplModule: Mod :=
         (BKMODULE {
        (BKMod (FIFO'mod d2eFifo :: nil))
    with (BKMod (FIFO'mod e2wFifo :: nil))
    with (BKMod (Memory'mod mem :: nil))
    with (BKMod (ProcRegs'mod rf :: nil))
    with (BKMod (Scoreboard'mod sb :: nil))
    with (BKMod (Empty'mod decoder :: nil))
    with (BKMod (Empty'mod executer :: nil))
    with (BKMod (Empty'mod writeback :: nil))
    }). (* mkProcImpl *)

(* Module mkProcImpl type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkProcImpl := Build_Empty mkProcImplModule%kami.
    End Section'mkProcImpl.
End module'mkProcImpl.

Definition mkProcImpl := module'mkProcImpl.mkProcImpl.
Hint Unfold mkProcImpl : ModuleDefs.
Hint Unfold module'mkProcImpl.mkProcImpl : ModuleDefs.
Hint Unfold module'mkProcImpl.mkProcImplModule : ModuleDefs.

