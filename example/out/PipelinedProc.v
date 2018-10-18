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

(* * interface ProcRegFile#(rfsz, datasz) *)
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

Definition D2EFields (addrsz : nat) (pgmsz : nat) (rfsz : nat) := (STRUCT {
    "addr" :: Bit addrsz;
    "arithOp" :: OpArithK;
    "dst" :: Bit rfsz;
    "op" :: OpK;
    "pc" :: Bit pgmsz;
    "src1" :: Bit rfsz;
    "src2" :: Bit rfsz}).
Definition D2E  (addrsz : nat) (pgmsz : nat) (rfsz : nat) := Struct (D2EFields addrsz pgmsz rfsz).

Module module'mkPipelinedDecoder.
    Section Section'mkPipelinedDecoder.
    Variable datasz : nat.
    Variable instsz : nat.
    Variable pgmsz : nat.
    Variable addrsz : nat.
    Variable rfsz : nat.
    Variable instancePrefix: string.
    Variable pcInit: ConstT (Bit pgmsz).
    Variable pgmInit: ConstT (Vector (Bit instsz) pgmsz).
    Variable dec: Decoder.
    Variable d2e: FIFO.
        (* method bindings *)
    Let pc := mkReg (Bit pgmsz) (instancePrefix--"pc") (pcInit)%bk.
    Let pc_read : string := (Reg'_read pc).
    Let pc_write : string := (Reg'_write pc).
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
        CallM pc_v : Bit pgmsz (* regRead *) <- pc_read();
               LET inst : Bit instsz <- ($$pgmInit@[#pc_v]);
       CallM op : OpK (* varbinding *) <-  decgetOp (#inst : Bit instsz);
       CallM arithOp : OpArithK (* varbinding *) <-  decgetArithOp (#inst : Bit instsz);
       CallM src1 : Bit rfsz (* varbinding *) <-  decgetSrc1 (#inst : Bit instsz);
       CallM src2 : Bit rfsz (* varbinding *) <-  decgetSrc2 (#inst : Bit instsz);
       CallM dst : Bit rfsz (* varbinding *) <-  decgetDst (#inst : Bit instsz);
       CallM addr : Bit addrsz (* varbinding *) <-  decgetAddr (#inst : Bit instsz);
       LET decoded : D2E addrsz pgmsz rfsz <- STRUCT { "addr" ::= (#addr); "arithOp" ::= (#arithOp); "dst" ::= (#dst); "op" ::= (#op); "pc" ::= (#pc_v); "src1" ::= (#src1); "src2" ::= (#src2)  }%kami_expr;
       CallM call1 : Void <-  d2eenq (#decoded : D2E addrsz pgmsz rfsz);
               CallM pc_write ( (#pc_v + $1) : Bit pgmsz );
        Retv ) (* rule decode *)
    }). (* mkPipelinedDecoder *)

(* Module mkPipelinedDecoder type Bit#(instsz) -> Vector#(TExp#(instsz), Bit#(instsz)) -> Decoder#(instsz, instsz, instsz) -> FIFO#(D2E#(instsz, instsz, instsz)) -> Module#(Empty) return type Vector#(TExp#(instsz), Bit#(instsz)) *)
    Definition mkPipelinedDecoder := Build_Empty mkPipelinedDecoderModule%kami.
    End Section'mkPipelinedDecoder.
End module'mkPipelinedDecoder.

Definition mkPipelinedDecoder := module'mkPipelinedDecoder.mkPipelinedDecoder.
Hint Unfold mkPipelinedDecoder : ModuleDefs.
Hint Unfold module'mkPipelinedDecoder.mkPipelinedDecoder : ModuleDefs.
Hint Unfold module'mkPipelinedDecoder.mkPipelinedDecoderModule : ModuleDefs.

(* * interface Scoreboard#(rfsz) *)
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
    Variable rfsz : nat.
    Variable instancePrefix: string.
        (* method bindings *)
    Let sbFlags := mkReg (Bit rfsz) (instancePrefix--"sbFlags") (Default)%bk.
    Let sbFlags_read : string := (Reg'_read sbFlags).
    Let sbFlags_write : string := (Reg'_write sbFlags).
    Definition mkScoreboardModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules sbFlags :: nil))
    with Method instancePrefix--"search1" (sidx : (Bit rfsz)) : Bool :=
    (
CallM sbFlags_v : Vector Bool rfsz (* methoddef regread *) <- sbFlags_read();
        LET flag : Bool <- (#sbFlags_v@[#sidx]);
        Ret #flag    )

    with Method instancePrefix--"search2" (sidx : (Bit rfsz)) : Bool :=
    (
CallM sbFlags_v : Vector Bool rfsz (* methoddef regread *) <- sbFlags_read();
        LET flag : Bool <- (#sbFlags_v@[#sidx]);
        Ret #flag    )

    with Method instancePrefix--"insert" (nidx : (Bit rfsz)) : Void :=
    (
      CallM sbFlags_v : Vector Bool rfsz (* methoddef regread *) <- sbFlags_read();
        LET flags : Vector Bool rfsz <- #sbFlags_v;
        LET newflags : Vector Bool rfsz <- #flags @[ #nidx <- $$true ];
        CallM sbFlags_write ( #newflags : Vector Bool rfsz );
        Retv    )

    with Method instancePrefix--"remove" (nidx : (Bit rfsz)) : Void :=
    (
      CallM sbFlags_v : Vector Bool rfsz (* methoddef regread *) <- sbFlags_read();
        LET flags : Vector Bool rfsz <- #sbFlags_v;
        LET newflags : Vector Bool rfsz <- #flags @[ #nidx <- $$false ];
        CallM sbFlags_write ( #flags : Vector Bool rfsz );
        Retv    )

    }). (* mkScoreboard *)

(* Module mkScoreboard type Module#(Scoreboard#(instsz)) return type Scoreboard#(instsz) *)
    Definition mkScoreboard := Build_Scoreboard mkScoreboardModule%kami (instancePrefix--"insert") (instancePrefix--"remove") (instancePrefix--"search1") (instancePrefix--"search2").
    End Section'mkScoreboard.
End module'mkScoreboard.

Definition mkScoreboard := module'mkScoreboard.mkScoreboard.
Hint Unfold mkScoreboard : ModuleDefs.
Hint Unfold module'mkScoreboard.mkScoreboard : ModuleDefs.
Hint Unfold module'mkScoreboard.mkScoreboardModule : ModuleDefs.

