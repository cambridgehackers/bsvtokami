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

Definition D2EFields := (STRUCT {
    "addr" :: Bit AddrSz;
    "arithOp" :: OpArithK;
    "dst" :: Bit RegFileSz;
    "op" :: OpK;
    "pc" :: Bit PgmSz;
    "src1" :: Bit RegFileSz;
    "src2" :: Bit RegFileSz}).
Definition D2E  := Struct (D2EFields).

(* * interface PipelinedDecoder *)
Record PipelinedDecoder := {
    PipelinedDecoder'modules: Modules;
}.

Hint Unfold PipelinedDecoder'modules : ModuleDefs.

Module module'mkPipelinedDecoder.
    Section Section'mkPipelinedDecoder.
    Variable instancePrefix: string.
    Variable pcInit: ConstT (Bit PgmSz).
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable d2e: FIFO.
        (* method bindings *)
    (* method binding *) Let pc := mkReg (Bit PgmSz) (instancePrefix--"pc") ($0)%bk.
    (* method binding *) Let pc_read : string := (Reg'_read pc).
    (* method binding *) Let pc_write : string := (Reg'_write pc).
    (* instance methods *)
    Let d2eenq : string := (FIFO'enq d2e).
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
       CallM call5 : Void <-  d2eenq (#decoded : D2E);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule decode *)
    }). (* mkPipelinedDecoder *)

(* Module mkPipelinedDecoder type Bit#(PgmSz) -> RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> FIFO#(D2E) -> Module#(PipelinedDecoder) return type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) *)
    Definition mkPipelinedDecoder := Build_PipelinedDecoder mkPipelinedDecoderModule%kami.
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
    (* method binding *) Let sbFlags := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"sbFlags").
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

Module module'mkExecuter.
    Section Section'mkExecuter.
    Variable instancePrefix: string.
    Variable d2eFifo: FIFO.
    Variable e2wFifo: FIFO.
    Variable sb: Scoreboard.
    Variable exec: Executer.
    Variable rf: ProcRegs.
    (* instance methods *)
    Let d2eFifodeq : string := (FIFO'deq d2eFifo).
    Let d2eFifofirst : string := (FIFO'first d2eFifo).
    Let e2wFifoenq : string := (FIFO'enq e2wFifo).
    Let execexecArith : string := (Executer'execArith exec).
    Let rfread1 : string := (ProcRegs'read1 rf).
    Let sbinsert : string := (Scoreboard'insert sb).
    Let sbsearch1 : string := (Scoreboard'search1 sb).
    Let sbsearch2 : string := (Scoreboard'search2 sb).
    Definition mkExecuterModule: Modules :=
         (BKMODULE {
        Rule instancePrefix--"executeArith" :=
    (
       CallM d2e : D2E (* varbinding *) <-  d2eFifofirst ();
       CallM call6 : Bool <-  sbsearch1 ((#d2e ! D2EFields @. "src1") : Bit RegFileSz);
       CallM call7 : Bool <-  sbsearch2 ((#d2e ! D2EFields @. "src2") : Bit RegFileSz);

        Assert(((((#d2e ! D2EFields @. "op") == $$opArith) && #call6) && #call7));
               CallM deq : Void (* actionBinding *) <- d2eFifodeq ();
               LET src1 : Bit RegFileSz <- (#d2e ! D2EFields @. "src1");
               LET src2 : Bit RegFileSz <- (#d2e ! D2EFields @. "src2");
               LET dst : Bit RegFileSz <- (#d2e ! D2EFields @. "dst");
               LET arithOp : OpArithK <- (#d2e ! D2EFields @. "arithOp");
       CallM val1 : Bit DataSz (* varbinding *) <-  rfread1 (#src1 : Bit RegFileSz);
       CallM val2 : Bit DataSz (* varbinding *) <-  rfread1 (#src2 : Bit RegFileSz);
       CallM execVal : Bit DataSz (* varbinding *) <-  execexecArith (#arithOp : OpArithK) (#val1 : Bit DataSz) (#val2 : Bit DataSz);
               CallM upd : Void (* actionBinding *) <- sbinsert (#dst : Bit RegFileSz);
               LET e2w : E2W <- STRUCT { "idx" ::= (#dst); "val" ::= (#execVal)  }%kami_expr;
               CallM enq : Void (* actionBinding *) <- e2wFifoenq (#e2w : E2W);
        Retv ) (* rule executeArith *)
    }). (* mkExecuter *)

(* Module mkExecuter type FIFO#(D2E) -> FIFO#(E2W) -> Scoreboard -> Executer -> ProcRegs -> Module#(Empty) return type FIFO#(E2W) *)
    Definition mkExecuter := Build_Empty mkExecuterModule%kami.
    End Section'mkExecuter.
End module'mkExecuter.

Definition mkExecuter := module'mkExecuter.mkExecuter.
Hint Unfold mkExecuter : ModuleDefs.
Hint Unfold module'mkExecuter.mkExecuter : ModuleDefs.
Hint Unfold module'mkExecuter.mkExecuterModule : ModuleDefs.

Module module'mkWriteBack.
    Section Section'mkWriteBack.
    Variable instancePrefix: string.
    Variable e2wFifo: FIFO.
    Variable sb: Scoreboard.
    Variable rf: ProcRegs.
    (* instance methods *)
    Let e2wFifodeq : string := (FIFO'deq e2wFifo).
    Let e2wFifofirst : string := (FIFO'first e2wFifo).
    Let rfwrite : string := (ProcRegs'write rf).
    Let sbremove : string := (Scoreboard'remove sb).
    Definition mkWriteBackModule: Modules :=
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
    }). (* mkWriteBack *)

(* Module mkWriteBack type FIFO#(E2W) -> Scoreboard -> ProcRegs -> Module#(Empty) return type Scoreboard *)
    Definition mkWriteBack := Build_Empty mkWriteBackModule%kami.
    End Section'mkWriteBack.
End module'mkWriteBack.

Definition mkWriteBack := module'mkWriteBack.mkWriteBack.
Hint Unfold mkWriteBack : ModuleDefs.
Hint Unfold module'mkWriteBack.mkWriteBack : ModuleDefs.
Hint Unfold module'mkWriteBack.mkWriteBackModule : ModuleDefs.

