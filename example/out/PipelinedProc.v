Require Import Bool String List Arith.
Require Import Omega.
Require Import micromega.Lia.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import FIFO.
Require Import ProcMemSpec.
Require Import RegFile.
(* * interface ProcRegs *)
Record ProcRegs := {
    ProcRegs'modules: Modules;
    ProcRegs'read1 : string;
    ProcRegs'read2 : string;
    ProcRegs'write : string;
}.

Hint Unfold ProcRegs'modules : ModuleDefs.
Hint Unfold ProcRegs'read1 : ModuleDefs.
Hint Unfold ProcRegs'read2 : ModuleDefs.
Hint Unfold ProcRegs'write : ModuleDefs.

Module module'mkProcRegs.
    Section Section'mkProcRegs.
    Variable instancePrefix: string.
        (* method bindings *)
    (* method binding *) Let rf := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"rf").
    (* instance methods *)
    Let rfsub : string := (RegFile'sub rf).
    Let rfupd : string := (RegFile'upd rf).
    Definition mkProcRegsModule: Modules :=
         (BKMODULE {
        (BKMod (RegFile'modules rf :: nil))
    with Method instancePrefix--"read1" (r1 : (Bit RegFileSz)) : Bit DataSz :=
    (
CallM val : Bit DataSz (* varbinding *) <-  rfsub (#r1 : Bit RegFileSz);
        Ret #val    )

    with Method instancePrefix--"read2" (r2 : (Bit RegFileSz)) : Bit DataSz :=
    (
CallM val : Bit DataSz (* varbinding *) <-  rfsub (#r2 : Bit RegFileSz);
        Ret #val    )

    with Method instancePrefix--"write" (r : (Bit RegFileSz)) (val : (Bit DataSz)) : Void :=
    (
        CallM written : Void (* actionBinding *) <- rfupd (#r : Bit RegFileSz) (#val : Bit DataSz);
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

Definition D2EFields := (STRUCT {
    "addr" :: Bit AddrSz;
    "arithOp" :: OpArithK;
    "dst" :: Bit RegFileSz;
    "op" :: OpK;
    "pc" :: Bit PgmSz;
    "src1" :: Bit RegFileSz;
    "src2" :: Bit RegFileSz}).
Definition D2E  := Struct (D2EFields).

Module module'mkPipelinedDecoder.
    Section Section'mkPipelinedDecoder.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable d2eFifo: FIFO.
        (* method bindings *)
    (* method binding *) Let pc := mkReg (Bit PgmSz) (instancePrefix--"pc") ($0)%bk.
    (* method binding *) Let pc_read : string := (Reg'_read pc).
    (* method binding *) Let pc_write : string := (Reg'_write pc).
    (* instance methods *)
    Let d2eFifoenq : string := (FIFO'enq d2eFifo).
    Let decgetAddr : string := (Decoder'getAddr dec).
    Let decgetArithOp : string := (Decoder'getArithOp dec).
    Let decgetDst : string := (Decoder'getDst dec).
    Let decgetOp : string := (Decoder'getOp dec).
    Let decgetSrc1 : string := (Decoder'getSrc1 dec).
    Let decgetSrc2 : string := (Decoder'getSrc2 dec).
    Let pgmsub : string := (RegFile'sub pgm).
    Definition mkPipelinedDecoderModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules pc :: nil))
    with Rule instancePrefix--"decode" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM op : OpK (* varbinding *) <-  decgetOp (#inst : Bit InstrSz);
       CallM arithOp : OpArithK (* varbinding *) <-  decgetArithOp (#inst : Bit InstrSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 (#inst : Bit InstrSz);
       CallM dst : Bit RegFileSz (* varbinding *) <-  decgetDst (#inst : Bit InstrSz);
       CallM addr : Bit AddrSz (* varbinding *) <-  decgetAddr (#inst : Bit InstrSz);
               LET decoded : D2E <- STRUCT { "addr" ::= (#addr); "arithOp" ::= (#arithOp); "dst" ::= (#dst); "op" ::= (#op); "pc" ::= (#pc_v); "src1" ::= (#src1); "src2" ::= (#src2)  }%kami_expr;
               CallM enq : Void (* actionBinding *) <- d2eFifoenq (#decoded : D2E);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
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
    Scoreboard'modules: Modules;
    Scoreboard'search1 : string;
    Scoreboard'search2 : string;
    Scoreboard'insert : string;
    Scoreboard'remove : string;
}.

Hint Unfold Scoreboard'modules : ModuleDefs.
Hint Unfold Scoreboard'search1 : ModuleDefs.
Hint Unfold Scoreboard'search2 : ModuleDefs.
Hint Unfold Scoreboard'insert : ModuleDefs.
Hint Unfold Scoreboard'remove : ModuleDefs.

Module module'mkScoreboard.
    Section Section'mkScoreboard.
    Variable instancePrefix: string.
        (* method bindings *)
    (* method binding *) Let sbFlags := mkRegFileFull (Bit RegFileSz) Bool (instancePrefix--"sbFlags").
    (* instance methods *)
    Let sbFlagssub : string := (RegFile'sub sbFlags).
    Let sbFlagsupd : string := (RegFile'upd sbFlags).
    Definition mkScoreboardModule: Modules :=
         (BKMODULE {
        (BKMod (RegFile'modules sbFlags :: nil))
    with Method instancePrefix--"search1" (sidx : (Bit RegFileSz)) : Bool :=
    (
CallM flag : Bool (* varbinding *) <-  sbFlagssub (#sidx : Bit RegFileSz);
        Ret #flag    )

    with Method instancePrefix--"search2" (sidx : (Bit RegFileSz)) : Bool :=
    (
CallM flag : Bool (* varbinding *) <-  sbFlagssub (#sidx : Bit RegFileSz);
        Ret #flag    )

    with Method instancePrefix--"insert" (nidx : (Bit RegFileSz)) : Void :=
    (
        CallM unused : Void (* actionBinding *) <- sbFlagsupd (#nidx : Bit RegFileSz) (($$true)%kami_expr : Bool);
        Retv    )

    with Method instancePrefix--"remove" (nidx : (Bit RegFileSz)) : Void :=
    (
        CallM unused : Void (* actionBinding *) <- sbFlagsupd (#nidx : Bit RegFileSz) (($$false)%kami_expr : Bool);
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

Definition E2WFields := (STRUCT {
    "idx" :: Bit RegFileSz;
    "val" :: Bit DataSz}).
Definition E2W  := Struct (E2WFields).

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
    Definition mkPipelinedExecuterModule: Modules :=
         (BKMODULE {
        Rule instancePrefix--"executeArith" :=
    (
       CallM d2e : D2E (* varbinding *) <-  d2eFifofirst ();
       CallM call5 : Bool <-  sbsearch1 ((#d2e ! D2EFields @. "src1") : Bit RegFileSz);
       CallM call6 : Bool <-  sbsearch2 ((#d2e ! D2EFields @. "src2") : Bit RegFileSz);

        Assert(((((#d2e ! D2EFields @. "op") == $$opArith) && (!#call5)) && (!#call6)));
               CallM deq : Void (* actionBinding *) <- d2eFifodeq ();
               LET src1 : Bit RegFileSz <- (#d2e ! D2EFields @. "src1");
               LET src2 : Bit RegFileSz <- (#d2e ! D2EFields @. "src2");
               LET dst : Bit RegFileSz <- (#d2e ! D2EFields @. "dst");
               LET arithOp : OpArithK <- (#d2e ! D2EFields @. "arithOp");
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
       CallM val2 : Bit DataSz (* varbinding *) <-  rfread2 (#src2 : Bit RegFileSz);
       CallM execVal : Bit DataSz (* varbinding *) <-  execexecArith (#arithOp : OpArithK) (#val1 : Bit DataSz) (#val2 : Bit DataSz);
               CallM upd : Void (* actionBinding *) <- sbinsert (#dst : Bit RegFileSz);
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst); "val" ::= (#execVal)  }%kami_expr;
               CallM enq : Void (* actionBinding *) <- e2wFifoenq (#e2w : E2W);
        Retv ) (* rule executeArith *)
    with Rule instancePrefix--"executeLoad" :=
    (
       CallM d2e : D2E (* varbinding *) <-  d2eFifofirst ();
       CallM call7 : Bool <-  sbsearch1 ((#d2e ! D2EFields @. "src1") : Bit RegFileSz);
       CallM call8 : Bool <-  sbsearch2 ((#d2e ! D2EFields @. "dst") : Bit RegFileSz);

        Assert(((((#d2e ! D2EFields @. "op") == $$opLd) && (!#call7)) && (!#call8)));
               CallM deq : Void (* actionBinding *) <- d2eFifodeq ();
               LET src1 : Bit RegFileSz <- (#d2e ! D2EFields @. "src1");
               LET dst : Bit RegFileSz <- (#d2e ! D2EFields @. "dst");
               LET addr : Bit AddrSz <- (#d2e ! D2EFields @. "addr");
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr); "data" ::= ($$(natToWord 32 0)); "isLoad" ::= ($$(natToWord 1 1))  }%kami_expr;
               CallM ldVal : Bit DataSz (* actionBinding *) <- memdoMem (#memrq : MemRq);
               CallM insert : Void (* actionBinding *) <- sbinsert (#dst : Bit RegFileSz);
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst); "val" ::= (#ldVal)  }%kami_expr;
               CallM enq : Void (* actionBinding *) <- e2wFifoenq (#e2w : E2W);
        Retv ) (* rule executeLoad *)
    with Rule instancePrefix--"executeStore" :=
    (
       CallM d2e : D2E (* varbinding *) <-  d2eFifofirst ();
       CallM call9 : Bool <-  sbsearch1 ((#d2e ! D2EFields @. "src1") : Bit RegFileSz);

        Assert((((#d2e ! D2EFields @. "op") == $$opSt) && (!#call9)));
               CallM deq : Void (* actionBinding *) <- d2eFifodeq ();
               LET src1 : Bit RegFileSz <- (#d2e ! D2EFields @. "src1");
               LET addr : Bit AddrSz <- (#d2e ! D2EFields @. "addr");
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
               LET memrq : MemRq <- STRUCT { "addr" ::= (#addr); "data" ::= (#val1); "isLoad" ::= ($$(natToWord 1 0))  }%kami_expr;
               CallM unused : Bit DataSz (* actionBinding *) <- memdoMem (#memrq : MemRq);
        Retv ) (* rule executeStore *)
    with Rule instancePrefix--"executeToHost" :=
    (
       CallM d2e : D2E (* varbinding *) <-  d2eFifofirst ();
       CallM call10 : Bool <-  sbsearch1 ((#d2e ! D2EFields @. "src1") : Bit RegFileSz);

        Assert((((#d2e ! D2EFields @. "op") == $$opTh) && (!#call10)));
               CallM deq : Void (* actionBinding *) <- d2eFifodeq ();
               LET src1 : Bit RegFileSz <- (#d2e ! D2EFields @. "src1");
               LET addr : Bit AddrSz <- (#d2e ! D2EFields @. "addr");
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
               CallM unused : Void (* actionBinding *) <- toHosttoHost (#val1 : Bit DataSz);
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
    Definition mkPipelinedWritebackModule: Modules :=
         (BKMODULE {
        Rule instancePrefix--"writeback" :=
    (
       CallM e2w : E2W (* varbinding *) <-  e2wFifofirst ();
               CallM deq : Void (* actionBinding *) <- e2wFifodeq ();
               LET idx : Bit RegFileSz <- (#e2w ! E2WFields @. "idx");
               LET val : Bit DataSz <- (#e2w ! E2WFields @. "val");
               CallM written : Void (* actionBinding *) <- rfwrite (#idx : Bit RegFileSz) (#val : Bit DataSz);
               CallM removed : Void (* actionBinding *) <- sbremove (#idx : Bit RegFileSz);
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
    (* method binding *) Let d2eFifo := mkFIFO D2E (instancePrefix--"d2eFifo").
    (* method binding *) Let e2wFifo := mkFIFO E2W (instancePrefix--"e2wFifo").
    (* method binding *) Let mem := mkMemory (instancePrefix--"mem").
    (* method binding *) Let rf := mkProcRegs (instancePrefix--"rf").
    (* method binding *) Let sb := mkScoreboard (instancePrefix--"sb").
    (* method binding *) Let decoder := mkPipelinedDecoder (instancePrefix--"decoder") (pgm)%bk (dec)%bk (d2eFifo)%bk.
    (* method binding *) Let executer := mkPipelinedExecuter (instancePrefix--"executer") (d2eFifo)%bk (e2wFifo)%bk (sb)%bk (exec)%bk (rf)%bk (mem)%bk (toHost)%bk.
    (* method binding *) Let writeback := mkPipelinedWriteback (instancePrefix--"writeback") (e2wFifo)%bk (sb)%bk (rf)%bk.
    Definition mkProcImplModule: Modules :=
         (BKMODULE {
        (BKMod (FIFO'modules d2eFifo :: nil))
    with (BKMod (FIFO'modules e2wFifo :: nil))
    with (BKMod (Memory'modules mem :: nil))
    with (BKMod (ProcRegs'modules rf :: nil))
    with (BKMod (Scoreboard'modules sb :: nil))
    with (BKMod (Empty'modules decoder :: nil))
    with (BKMod (Empty'modules executer :: nil))
    with (BKMod (Empty'modules writeback :: nil))
    }). (* mkProcImpl *)

(* Module mkProcImpl type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkProcImpl := Build_Empty mkProcImplModule%kami.
    End Section'mkProcImpl.
End module'mkProcImpl.

Definition mkProcImpl := module'mkProcImpl.mkProcImpl.
Hint Unfold mkProcImpl : ModuleDefs.
Hint Unfold module'mkProcImpl.mkProcImpl : ModuleDefs.
Hint Unfold module'mkProcImpl.mkProcImplModule : ModuleDefs.

