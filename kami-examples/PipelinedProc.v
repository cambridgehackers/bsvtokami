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
    Let (* action binding *) rf := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"rf").
    (* instance methods *)
    Let rf'sub : string := (RegFile'sub rf).
    Let rf'upd : string := (RegFile'upd rf).
    Local Open Scope kami_expr.

    Definition mkProcRegsModule: Mod :=
         (BKMODULE {
        (BKMod (RegFile'mod rf :: nil))
    with Method (instancePrefix--"read1") (r1 : (Bit RegFileSz)) : Bit DataSz :=
    (
BKCall val : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#r1) : Bit RegFileSz) ;
        Ret #val    )

    with Method (instancePrefix--"read2") (r2 : (Bit RegFileSz)) : Bit DataSz :=
    (
BKCall val : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#r2) : Bit RegFileSz) ;
        Ret #val    )

    with Method (instancePrefix--"write") ( params : write'paramsT )  : Void :=
    (
        LET r : (Bit RegFileSz) <- #params @% "_1" ;
        LET val : (Bit DataSz) <- #params @% "_2" ;
        BKCall written : Void (* actionBinding *) <- rf'upd ((#r) : Bit RegFileSz) ((#val) : Bit DataSz) ;
        Retv    )

    }). (* mkProcRegs *)

    Close Scope kami_expr.

    Hint Unfold mkProcRegsModule : ModuleDefs.
(* Module mkProcRegs type Module#(ProcRegs) return type ProcRegs *)
    Definition mkProcRegs := Build_ProcRegs mkProcRegsModule (instancePrefix--"read1") (instancePrefix--"read2") (instancePrefix--"write").
    Hint Unfold mkProcRegs : ModuleDefs.
    Hint Unfold mkProcRegsModule : ModuleDefs.

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
    Let pc : string := instancePrefix--"pc".
    (* instance methods *)
    Let d2eFifo'enq : string := (FIFO'enq d2eFifo).
    Let dec'getAddr : string := (Decoder'getAddr dec).
    Let dec'getArithOp : string := (Decoder'getArithOp dec).
    Let dec'getDst : string := (Decoder'getDst dec).
    Let dec'getOp : string := (Decoder'getOp dec).
    Let dec'getSrc1 : string := (Decoder'getSrc1 dec).
    Let dec'getSrc2 : string := (Decoder'getSrc2 dec).
    Let pgm'sub : string := (RegFile'sub pgm).
    Local Open Scope kami_expr.

    Definition mkPipelinedDecoderModule: Mod :=
         (BKMODULE {
        Register pc : Bit PgmSz <-  (* intwidth *) (natToWord PgmSz 0)
    with Rule instancePrefix--"decode" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall op : OpK (* varbinding *) <-  (* translateCall *) dec'getOp ((#inst) : Bit InstrSz) ;
       BKCall arithOp : OpArithK (* varbinding *) <-  (* translateCall *) dec'getArithOp ((#inst) : Bit InstrSz) ;
       BKCall src1 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getSrc1 ((#inst) : Bit InstrSz) ;
       BKCall src2 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getSrc2 ((#inst) : Bit InstrSz) ;
       BKCall dst : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getDst ((#inst) : Bit InstrSz) ;
       BKCall addr : Bit AddrSz (* varbinding *) <-  (* translateCall *) dec'getAddr ((#inst) : Bit InstrSz) ;
               LET decoded : D2E (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "arithOp" ::= (#arithOp) ; "dst" ::= (#dst) ; "op" ::= (#op) ; "pc" ::= (#pc_v) ; "src1" ::= (#src1) ; "src2" ::= (#src2)  }%kami_expr ;
               BKCall enq : Void (* actionBinding *) <- d2eFifo'enq ((#decoded) : D2E) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decode *)
    }). (* mkPipelinedDecoder *)

    Close Scope kami_expr.

    Hint Unfold mkPipelinedDecoderModule : ModuleDefs.
(* Module mkPipelinedDecoder type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> FIFO#(D2E) -> Module#(Empty) return type Decoder *)
    Definition mkPipelinedDecoder := Build_Empty mkPipelinedDecoderModule.
    Hint Unfold mkPipelinedDecoder : ModuleDefs.
    Hint Unfold mkPipelinedDecoderModule : ModuleDefs.

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
    Let (* action binding *) sbFlags := mkRegFileFull (Bit RegFileSz) (Bool) (instancePrefix--"sbFlags").
    (* instance methods *)
    Let sbFlags'sub : string := (RegFile'sub sbFlags).
    Let sbFlags'upd : string := (RegFile'upd sbFlags).
    Local Open Scope kami_expr.

    Definition mkScoreboardModule: Mod :=
         (BKMODULE {
        (BKMod (RegFile'mod sbFlags :: nil))
    with Method (instancePrefix--"search1") (sidx : (Bit RegFileSz)) : Bool :=
    (

        Assert(($$true)%kami_expr) ;
BKCall flag : Bool (* varbinding *) <-  (* translateCall *) sbFlags'sub ((#sidx) : Bit RegFileSz) ;
        Ret #flag    )

    with Method (instancePrefix--"search2") (sidx : (Bit RegFileSz)) : Bool :=
    (
BKCall flag : Bool (* varbinding *) <-  (* translateCall *) sbFlags'sub ((#sidx) : Bit RegFileSz) ;
        Ret #flag    )

    with Method (instancePrefix--"insert") (nidx : (Bit RegFileSz)) : Void :=
    (
        BKCall unused : Void (* actionBinding *) <- sbFlags'upd ((#nidx) : Bit RegFileSz) ((($$true)%kami_expr) : Bool) ;
        Retv    )

    with Method (instancePrefix--"remove") (nidx : (Bit RegFileSz)) : Void :=
    (
        BKCall unused : Void (* actionBinding *) <- sbFlags'upd ((#nidx) : Bit RegFileSz) ((($$false)%kami_expr) : Bool) ;
        Retv    )

    }). (* mkScoreboard *)

    Close Scope kami_expr.

    Hint Unfold mkScoreboardModule : ModuleDefs.
(* Module mkScoreboard type Module#(Scoreboard) return type Scoreboard *)
    Definition mkScoreboard := Build_Scoreboard mkScoreboardModule (instancePrefix--"insert") (instancePrefix--"remove") (instancePrefix--"search1") (instancePrefix--"search2").
    Hint Unfold mkScoreboard : ModuleDefs.
    Hint Unfold mkScoreboardModule : ModuleDefs.

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
    Let d2eFifo'deq : string := (FIFO'deq d2eFifo).
    Let d2eFifo'first : string := (FIFO'first d2eFifo).
    Let e2wFifo'enq : string := (FIFO'enq e2wFifo).
    Let exec'execArith : string := (Executer'execArith exec).
    Let mem'doMem : string := (Memory'doMem mem).
    Let rf'read1 : string := (ProcRegs'read1 rf).
    Let rf'read2 : string := (ProcRegs'read2 rf).
    Let sb'insert : string := (Scoreboard'insert sb).
    Let sb'search1 : string := (Scoreboard'search1 sb).
    Let sb'search2 : string := (Scoreboard'search2 sb).
    Let toHost'toHost : string := (ToHost'toHost toHost).
    Local Open Scope kami_expr.

    Definition mkPipelinedExecuterModule: Mod :=
         (BKMODULE {
        Rule instancePrefix--"executeArith" :=
    (
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
       BKCall call9 : Bool <-  (* translateCall *) sb'search1 (((#d2e @% "src1")) : Bit RegFileSz) ;
       BKCall call10 : Bool <-  (* translateCall *) sb'search2 (((#d2e @% "src2")) : Bit RegFileSz) ;

        Assert(((((#d2e @% "op") == $$ (* isConstT *)opArith) && (!#call9)) && (!#call10))) ;
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
               BKCall deq : Void (* actionBinding *) <- d2eFifo'deq () ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET src2 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src2") ;
               LET dst : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "dst") ;
               LET arithOp : OpArithK (* non-call varbinding *) <- (#d2e @% "arithOp") ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'read1 ((#src1) : Bit RegFileSz) ;
       BKCall val2 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'read2 ((#src2) : Bit RegFileSz) ;
       BKCall execVal : Bit DataSz (* varbinding *) <-  (* translateCall *) exec'execArith ((#arithOp) : OpArithK) ((#val1) : Bit DataSz) ((#val2) : Bit DataSz) ;
               BKCall upd : Void (* actionBinding *) <- sb'insert ((#dst) : Bit RegFileSz) ;
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               BKCall enq : Void (* actionBinding *) <- e2wFifo'enq ((#e2w) : E2W) ;
        Retv ) (* rule executeArith *)
    with Rule instancePrefix--"executeLoad" :=
    (
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
       BKCall call11 : Bool <-  (* translateCall *) sb'search1 (((#d2e @% "src1")) : Bit RegFileSz) ;
       BKCall call12 : Bool <-  (* translateCall *) sb'search2 (((#d2e @% "dst")) : Bit RegFileSz) ;

        Assert(((((#d2e @% "op") == $$ (* isConstT *)opLd) && (!#call11)) && (!#call12))) ;
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
               BKCall deq : Void (* actionBinding *) <- d2eFifo'deq () ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET dst : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "dst") ;
               LET addr : Bit AddrSz (* non-call varbinding *) <- (#d2e @% "addr") ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'read1 ((#src1) : Bit RegFileSz) ;
               LET memrq : MemRq (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "data" ::= ($$ (* intwidth *) (natToWord 32 0)) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 1))  }%kami_expr ;
               BKCall ldVal : Bit DataSz (* actionBinding *) <- mem'doMem ((#memrq) : MemRq) ;
               BKCall insert : Void (* actionBinding *) <- sb'insert ((#dst) : Bit RegFileSz) ;
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#ldVal)  }%kami_expr ;
               BKCall enq : Void (* actionBinding *) <- e2wFifo'enq ((#e2w) : E2W) ;
        Retv ) (* rule executeLoad *)
    with Rule instancePrefix--"executeStore" :=
    (
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
       BKCall call13 : Bool <-  (* translateCall *) sb'search1 (((#d2e @% "src1")) : Bit RegFileSz) ;

        Assert((((#d2e @% "op") == $$ (* isConstT *)opSt) && (!#call13))) ;
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
               BKCall deq : Void (* actionBinding *) <- d2eFifo'deq () ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET addr : Bit AddrSz (* non-call varbinding *) <- (#d2e @% "addr") ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'read1 ((#src1) : Bit RegFileSz) ;
               LET memrq : MemRq (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 0))  }%kami_expr ;
               BKCall unused : Bit DataSz (* actionBinding *) <- mem'doMem ((#memrq) : MemRq) ;
        Retv ) (* rule executeStore *)
    with Rule instancePrefix--"executeToHost" :=
    (
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
       BKCall call14 : Bool <-  (* translateCall *) sb'search1 (((#d2e @% "src1")) : Bit RegFileSz) ;

        Assert((((#d2e @% "op") == $$ (* isConstT *)opTh) && (!#call14))) ;
       BKCall d2e : D2E (* varbinding *) <-  (* translateCall *) d2eFifo'first () ;
               BKCall deq : Void (* actionBinding *) <- d2eFifo'deq () ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET addr : Bit AddrSz (* non-call varbinding *) <- (#d2e @% "addr") ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'read1 ((#src1) : Bit RegFileSz) ;
               BKCall unused : Void (* actionBinding *) <- toHost'toHost ((#val1) : Bit DataSz) ;
        Retv ) (* rule executeToHost *)
    }). (* mkPipelinedExecuter *)

    Close Scope kami_expr.

    Hint Unfold mkPipelinedExecuterModule : ModuleDefs.
(* Module mkPipelinedExecuter type FIFO#(D2E) -> FIFO#(E2W) -> Scoreboard -> Executer -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type FIFO#(E2W) *)
    Definition mkPipelinedExecuter := Build_Empty mkPipelinedExecuterModule.
    Hint Unfold mkPipelinedExecuter : ModuleDefs.
    Hint Unfold mkPipelinedExecuterModule : ModuleDefs.

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
    Let e2wFifo'deq : string := (FIFO'deq e2wFifo).
    Let e2wFifo'first : string := (FIFO'first e2wFifo).
    Let rf'write : string := (ProcRegs'write rf).
    Let sb'remove : string := (Scoreboard'remove sb).
    Local Open Scope kami_expr.

    Definition mkPipelinedWritebackModule: Mod :=
         (BKMODULE {
        Rule instancePrefix--"writeback" :=
    (
       BKCall e2w : E2W (* varbinding *) <-  (* translateCall *) e2wFifo'first () ;
               BKCall deq : Void (* actionBinding *) <- e2wFifo'deq () ;
               LET idx : Bit RegFileSz (* non-call varbinding *) <- (#e2w @% "idx") ;
               LET val : Bit DataSz (* non-call varbinding *) <- (#e2w @% "val") ;
               BKCall written : Void (* actionBinding *) <- rf'write ((#idx) : Bit RegFileSz) ((#val) : Bit DataSz) ;
               BKCall removed : Void (* actionBinding *) <- sb'remove ((#idx) : Bit RegFileSz) ;
        Retv ) (* rule writeback *)
    }). (* mkPipelinedWriteback *)

    Close Scope kami_expr.

    Hint Unfold mkPipelinedWritebackModule : ModuleDefs.
(* Module mkPipelinedWriteback type FIFO#(E2W) -> Scoreboard -> ProcRegs -> Module#(Empty) return type Scoreboard *)
    Definition mkPipelinedWriteback := Build_Empty mkPipelinedWritebackModule.
    Hint Unfold mkPipelinedWriteback : ModuleDefs.
    Hint Unfold mkPipelinedWritebackModule : ModuleDefs.

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
    Let (* action binding *) d2eFifo := mkFIFO (D2E) (instancePrefix--"d2eFifo").
    Let (* action binding *) e2wFifo := mkFIFO (E2W) (instancePrefix--"e2wFifo").
    Let (* action binding *) mem := mkMemory (instancePrefix--"mem").
    Let (* action binding *) rf := mkProcRegs (instancePrefix--"rf").
    Let (* action binding *) sb := mkScoreboard (instancePrefix--"sb").
    Let (* action binding *) decoder := mkPipelinedDecoder (instancePrefix--"decoder") (pgm)%bk (dec)%bk (d2eFifo)%bk.
    Let (* action binding *) executer := mkPipelinedExecuter (instancePrefix--"executer") (d2eFifo)%bk (e2wFifo)%bk (sb)%bk (exec)%bk (rf)%bk (mem)%bk (toHost)%bk.
    Let (* action binding *) writeback := mkPipelinedWriteback (instancePrefix--"writeback") (e2wFifo)%bk (sb)%bk (rf)%bk.
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

    Close Scope kami_expr.

    Hint Unfold mkProcImplModule : ModuleDefs.
(* Module mkProcImpl type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkProcImpl := Build_Empty mkProcImplModule.
    Hint Unfold mkProcImpl : ModuleDefs.
    Hint Unfold mkProcImplModule : ModuleDefs.

    End Section'mkProcImpl.
End module'mkProcImpl.

Definition mkProcImpl := module'mkProcImpl.mkProcImpl.
Hint Unfold mkProcImpl : ModuleDefs.
Hint Unfold module'mkProcImpl.mkProcImpl : ModuleDefs.
Hint Unfold module'mkProcImpl.mkProcImplModule : ModuleDefs.

