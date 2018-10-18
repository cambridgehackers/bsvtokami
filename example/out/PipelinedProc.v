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

(* * interface ProcRegFile *)
Record ProcRegFile := {
    ProcRegFile'modules: Modules;
    ProcRegFile'read1 : string;
    ProcRegFile'read2 : string;
    ProcRegFile'write : string;
}.

Hint Unfold ProcRegFile'modules : ModuleDefs.
Hint Unfold ProcRegFile'read1 : ModuleDefs.
Hint Unfold ProcRegFile'read2 : ModuleDefs.
Hint Unfold ProcRegFile'write : ModuleDefs.

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
    Variable pgmInit: ConstT (Vector (Bit InstrSz) PgmSz).
    Variable dec: Decoder.
    Variable d2e: FIFO.
        (* method bindings *)
    (* method binding *) Let pc := mkReg (Bit PgmSz) (instancePrefix--"pc") (pcInit)%bk.
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
    Definition mkPipelinedDecoderModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules pc :: nil))
    with Rule instancePrefix--"decode" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
               LET inst : Bit InstrSz <- ($$pgmInit@[#pc_v]);
       CallM op : OpK (* varbinding *) <-  decgetOp (#inst : Bit InstrSz);
       CallM arithOp : OpArithK (* varbinding *) <-  decgetArithOp (#inst : Bit InstrSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 (#inst : Bit InstrSz);
       CallM dst : Bit RegFileSz (* varbinding *) <-  decgetDst (#inst : Bit InstrSz);
       CallM addr : Bit AddrSz (* varbinding *) <-  decgetAddr (#inst : Bit InstrSz);
               LET decoded : D2E <- STRUCT { "addr" ::= (#addr); "arithOp" ::= (#arithOp); "dst" ::= (#dst); "op" ::= (#op); "pc" ::= (#pc_v); "src1" ::= (#src1); "src2" ::= (#src2)  }%kami_expr;
       CallM call1 : Void <-  d2eenq (#decoded : D2E);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule decode *)
    }). (* mkPipelinedDecoder *)

(* Module mkPipelinedDecoder type Bit#(PgmSz) -> Vector#(TExp#(PgmSz), Bit#(InstrSz)) -> Decoder -> FIFO#(D2E) -> Module#(PipelinedDecoder) return type Vector#(TExp#(PgmSz), Bit#(InstrSz)) *)
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
    (* method binding *) Let sbFlags := mkReg (Bit RegFileSz) (instancePrefix--"sbFlags") ($$(natToWord RegFileSz 0))%bk.
    (* method binding *) Let sbFlags_read : string := (Reg'_read sbFlags).
    (* method binding *) Let sbFlags_write : string := (Reg'_write sbFlags).
    Definition mkScoreboardModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules sbFlags :: nil))
    with Method instancePrefix--"search1" (sidx : (Bit RegFileSz)) : Bool :=
    (
CallM sbFlags_v : Vector Bool RegFileSz (* methoddef regread *) <- sbFlags_read();
        LET flag : Bool <- (#sbFlags_v@[#sidx]);
        Ret #flag    )

    with Method instancePrefix--"search2" (sidx : (Bit RegFileSz)) : Bool :=
    (
CallM sbFlags_v : Vector Bool RegFileSz (* methoddef regread *) <- sbFlags_read();
        LET flag : Bool <- (#sbFlags_v@[#sidx]);
        Ret #flag    )

    with Method instancePrefix--"insert" (nidx : (Bit RegFileSz)) : Void :=
    (
CallM sbFlags_v : Vector Bool RegFileSz (* methoddef regread *) <- sbFlags_read();
        LET flags : Vector Bool RegFileSz <- #sbFlags_v;
        LET newflags : Vector Bool RegFileSz <- #flags @[ #nidx <- $$true ];
        CallM sbFlags_write ( #newflags : Vector Bool RegFileSz );
        Retv    )

    with Method instancePrefix--"remove" (nidx : (Bit RegFileSz)) : Void :=
    (
CallM sbFlags_v : Vector Bool RegFileSz (* methoddef regread *) <- sbFlags_read();
        LET flags : Vector Bool RegFileSz <- #sbFlags_v;
        LET newflags : Vector Bool RegFileSz <- #flags @[ #nidx <- $$false ];
        CallM sbFlags_write ( #newflags : Vector Bool RegFileSz );
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

