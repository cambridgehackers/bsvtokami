Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.
Require Import Decoder.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import FIFO.
Require Import RegFile.
Require Import ProcMemSpec.
Require Import PipelinedProc.
Require Import Vector.
Module module'mkDecExec.
    Section Section'mkDecExec.
    Variable instancePrefix: string.
    Variable pgm: string.
    Variable dec: Decoder.Decoder.
    Variable exec: Decoder.Executer.
    Variable e2wFifo_reg: string.
    Variable e2wFifo_valid: string.
    Variable rf: string.
    Variable mem: string.
    Variable toHost: string.
        (* method bindings *)
    Let pc : string := instancePrefix--"pc".
    Let sbFlags : string := instancePrefix--"sbFlags".
    (* instance methods *)
    Let mem'doMem : string := mem--"doMem".
    Let toHost'toHost : string := toHost--"toHost".
    Local Open Scope kami_expr.

    Definition mkDecExecModule: Mod :=
         (BKMODULE {
        Register pc : Bit PgmSz <- natToWord PgmSz 0
    with Register sbFlags : Array NumRegs Bool <- Default
    with Rule instancePrefix--"decexecArith" :=
    (
        Read e2wFifo_valid_v : Bool <- e2wFifo_valid ;
        Read pc_v : Bit PgmSz <- pc ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET call17 : Bit InstrSz <- #instrs @[  #pc_v ] ;
       LET call16 : Bool <- (getOp dec _ call17) == $$opArith ;
       LET call19 : Bit InstrSz <- #instrs @[ #pc_v ] ;
       LET call18 : Bit RegFileSz <-  getSrc1 dec _ call19 ;
       LET call21 : Bit InstrSz <-  #instrs @[ #pc_v ] ;
       LET call20 : Bit RegFileSz <-  getSrc2 dec _ call21 ;

        Assert((((#call16 && (!(#sbFlags_v @[ #call18 ]))) && (!(#sbFlags_v @[ #call20 ]))) && (!#e2wFifo_valid_v))) ;
       LET inst : Bit InstrSz (* varbinding *) <-  #instrs @[ #pc_v ] ;
       LET src1 : Bit RegFileSz (* varbinding *) <-  getSrc1 dec _ inst ;
       LET src2 : Bit RegFileSz (* varbinding *) <-  getSrc2 dec _ inst ;
       LET dst : Bit RegFileSz (* varbinding *) <-  getDst dec _ inst ;
       LET arithOp : OpArithK (* varbinding *) <- getArithOp dec _ inst ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;
       LET val2 : Bit DataSz (* varbinding *) <-  #regsval @[ #src2 ] ;
       LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2) ;
               LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
               LET flags : Array NumRegs Bool <- #flags @[#dst <- $$true] ;
               Write sbFlags : Array NumRegs Bool <- #flags ;
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               Write e2wFifo_reg : E2W <- #e2w ;
               Write e2wFifo_valid : Bool <- ($$true)%kami_expr ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decexecArith *)
    with Rule instancePrefix--"decexecLd" :=
    (
        Read e2wFifo_valid_v : Bool <- e2wFifo_valid ;
        Read pc_v : Bit PgmSz <- pc ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET call23 : Bit InstrSz <- #instrs @[ #pc_v ] ;
       LET call22 : Bool <-  (getOp dec _ call23) == $$opLd ;
       LET call25 : Bit InstrSz <-  #instrs @[ #pc_v ] ;
       LET call24 : Bit RegFileSz <-  getDst dec _ call25 ;

        Assert(((#call22 && (!(#sbFlags_v @[ #call24 ]))) && (!#e2wFifo_valid_v))) ;
       LET inst : Bit InstrSz (* varbinding *) <- #instrs @[ #pc_v ] ;
       LET src1 : Bit RegFileSz (* varbinding *) <-  getSrc1 dec _ inst ;
       LET dst : Bit RegFileSz (* varbinding *) <-  getDst dec _ inst ;
       LET addr : Bit AddrSz (* varbinding *) <- getAddr dec _ inst ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;

               LET memrq : MemRq (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 1))  }%kami_expr ;
               BKCall ldVal : Bit DataSz (* actionBinding *) <- mem'doMem ((#memrq) : MemRq) ;
               LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
               LET flags : Array NumRegs Bool <- #flags @[#dst <- $$true ] ;
               Write sbFlags : Array NumRegs Bool <- #flags ;
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#ldVal)  }%kami_expr ;
               Write e2wFifo_reg : E2W <- #e2w ;
               Write e2wFifo_valid : Bool <- ($$true)%kami_expr ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decexecLd *)
    with Rule instancePrefix--"decexecSt" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET call27 : Bit InstrSz <-  #instrs @[ #pc_v ] ;
       LET call26 : Bool <-  (getOp dec _ call27)  == $$opSt ;

        Assert(#call26) ;
       LET inst : Bit InstrSz (* varbinding *) <- #instrs @[ #pc_v ] ;
       LET src1 : Bit RegFileSz (* varbinding *) <- getSrc1 dec _ inst ;
       LET addr : Bit AddrSz (* varbinding *) <-  getAddr dec _ inst ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;
               LET memrq : MemRq (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 0))  }%kami_expr ;
               BKCall unused : Bit DataSz (* actionBinding *) <- mem'doMem ((#memrq) : MemRq) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decexecSt *)
    with Rule instancePrefix--"decexecToHost" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET call29 : Bit InstrSz <-  #instrs @[  #pc_v ] ;
       LET call28 : Bool <-  (getOp dec _ call29) == $$opTh ;
       LET call31 : Bit InstrSz <-  #instrs @[ #pc_v ] ;
       LET call30 : Bit RegFileSz <-  getSrc1 dec _ call31 ;

        Assert((#call28 && (!(#sbFlags_v @[ #call30 ])))) ;
       LET inst : Bit InstrSz (* varbinding *) <-  #instrs @[ #pc_v ] ;
       LET src1 : Bit RegFileSz (* varbinding *) <- getSrc1 dec _ inst ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;

               BKCall unused : Void (* actionBinding *) <- toHost'toHost ((#val1) : Bit DataSz) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decexecToHost *)
    }). (* mkDecExec *)

    Hint Unfold mkDecExecModule : ModuleDefs.
(* Module mkDecExec type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> Reg#(E2W) -> Reg#(Bool) -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkDecExec := Build_Empty mkDecExecModule.
    Hint Unfold mkDecExec : ModuleDefs.
    Hint Unfold mkDecExecModule : ModuleDefs.

    End Section'mkDecExec.
End module'mkDecExec.

Definition mkDecExec := module'mkDecExec.mkDecExec.
Hint Unfold mkDecExec : ModuleDefs.
Hint Unfold module'mkDecExec.mkDecExec : ModuleDefs.
Hint Unfold module'mkDecExec.mkDecExecModule : ModuleDefs.

Module module'mkDecExecSep.
    Section Section'mkDecExecSep.
    Variable instancePrefix: string.
    Variable pgm: string.
    Variable dec: Decoder.Decoder.
    Variable exec: Decoder.Executer.
    Variable rf: string.
    Variable mem: string.
    Variable toHost: string.
        (* method bindings *)
    Let d2eFifo_reg : string := instancePrefix--"d2eFifo_reg".
    Let d2eFifo_valid : string := instancePrefix--"d2eFifo_valid".
    Let e2wFifo_reg : string := instancePrefix--"e2wFifo_reg".
    Let e2wFifo_valid : string := instancePrefix--"e2wFifo_valid".
    Let decoder_pc : string := instancePrefix--"decoder_pc".
    Let sbFlags : string := instancePrefix--"sbFlags".
    (* instance methods *)
    Let mem'doMem : string := mem--"doMem".
    Let toHost'toHost : string := toHost--"toHost".
    Local Open Scope kami_expr.

    Definition mkDecExecSepModule: Mod :=
         (BKMODULE {
        Register d2eFifo_reg : D2E <- Default
    with Register d2eFifo_valid : Bool <- (false)%kami_expr
    with Register e2wFifo_reg : E2W <- Default
    with Register e2wFifo_valid : Bool <- (false)%kami_expr
    with Register decoder_pc : Bit PgmSz <-  (* intwidth *) (natToWord PgmSz 0)
    with Register sbFlags : Array NumRegs Bool <- Default
    with Rule instancePrefix--"decode" :=
    (
        Read d2eFifo_valid_v : Bool <- d2eFifo_valid ;
        Read decoder_pc_v : Bit PgmSz <- decoder_pc ;
        Read d2eFifo_reg_v : D2E <- d2eFifo_reg ;
               LET d2e : D2E (* non-call varbinding *) <- #d2eFifo_reg_v ;

        Assert((!#d2eFifo_valid_v)) ;
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET inst : Bit InstrSz <- #instrs @[ #decoder_pc_v ] ;
       LET op : OpK (* varbinding *) <-  getOp dec _ inst ;
       LET arithOp : OpArithK (* varbinding *) <-  getArithOp dec _ inst ;
       LET src1 : Bit RegFileSz (* varbinding *) <-  getSrc1 dec _ inst ;
       LET src2 : Bit RegFileSz (* varbinding *) <-  getSrc2 dec _ inst ;
       LET dst : Bit RegFileSz (* varbinding *) <-  getDst dec _ inst ;
       LET addr : Bit AddrSz (* varbinding *) <- getAddr dec _ inst ;
               LET decoded : D2E (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "arithOp" ::= (#arithOp) ; "dst" ::= (#dst) ; "op" ::= (#op) ; "pc" ::= (#decoder_pc_v) ; "src1" ::= (#src1) ; "src2" ::= (#src2)  }%kami_expr ;
               Write d2eFifo_reg : D2E <- #decoded ;
               Write d2eFifo_valid : Bool <- ($$true)%kami_expr ;
               Write decoder_pc : Bit PgmSz <- (#decoder_pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decode *)
    with Rule instancePrefix--"executeArith" :=
    (
        Read d2eFifo_valid_v : Bool <- d2eFifo_valid ;
        Read e2wFifo_valid_v : Bool <- e2wFifo_valid ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
        Read d2eFifo_reg_v : D2E <- d2eFifo_reg ;
               LET d2e : D2E (* non-call varbinding *) <- #d2eFifo_reg_v ;

        Assert(((((((#d2e @% "op") == $$ (* isConstT *)opArith) && (!(#sbFlags_v @[ (#d2e @% "src1") ]))) && (!(#sbFlags_v @[ (#d2e @% "src2") ]))) && #d2eFifo_valid_v) && (!#e2wFifo_valid_v))) ;
               Write d2eFifo_valid : Bool <- ($$false)%kami_expr ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET src2 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src2") ;
               LET dst : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "dst") ;
               LET arithOp : OpArithK (* non-call varbinding *) <- (#d2e @% "arithOp") ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;
       LET val2 : Bit DataSz (* varbinding *) <-  #regsval @[ #src2 ] ;

       LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2) ;
               LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
               LET flags : Array NumRegs Bool <- #flags @[#dst <- $$true ] ;
               Write sbFlags : Array NumRegs Bool <- #flags ;
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               Write e2wFifo_reg : E2W <- #e2w ;
               Write e2wFifo_valid : Bool <- ($$true)%kami_expr ;
        Retv ) (* rule executeArith *)
    with Rule instancePrefix--"executeLoad" :=
    (
        Read d2eFifo_valid_v : Bool <- d2eFifo_valid ;
        Read e2wFifo_valid_v : Bool <- e2wFifo_valid ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
        Read d2eFifo_reg_v : D2E <- d2eFifo_reg ;
               LET d2e : D2E (* non-call varbinding *) <- #d2eFifo_reg_v ;

        Assert(((((((#d2e @% "op") == $$ (* isConstT *)opLd) && (!(#sbFlags_v @[ (#d2e @% "src1") ]))) && (!(#sbFlags_v @[ (#d2e @% "dst") ]))) && #d2eFifo_valid_v) && (!#e2wFifo_valid_v))) ;
               Write d2eFifo_valid : Bool <- ($$false)%kami_expr ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET dst : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "dst") ;
               LET addr : Bit AddrSz (* non-call varbinding *) <- (#d2e @% "addr") ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;

               LET memrq : MemRq (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "data" ::= ($$ (* intwidth *) (natToWord 32 0)) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 1))  }%kami_expr ;
               BKCall ldVal : Bit DataSz (* actionBinding *) <- mem'doMem ((#memrq) : MemRq) ;
               LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
               LET flags : Array NumRegs Bool <- #flags @[ #dst <- $$true ] ;
               Write sbFlags : Array NumRegs Bool <- #flags ;
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#ldVal)  }%kami_expr ;
               Write e2wFifo_reg : E2W <- #e2w ;
               Write e2wFifo_valid : Bool <- ($$true)%kami_expr ;
        Retv ) (* rule executeLoad *)
    with Rule instancePrefix--"executeStore" :=
    (
        Read d2eFifo_valid_v : Bool <- d2eFifo_valid ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
        Read d2eFifo_reg_v : D2E <- d2eFifo_reg ;
               LET d2e : D2E (* non-call varbinding *) <- #d2eFifo_reg_v ;

        Assert(((((#d2e @% "op") == $$ (* isConstT *)opSt) && (!(#sbFlags_v @[ (#d2e @% "src1") ]))) && #d2eFifo_valid_v)) ;
               Write d2eFifo_valid : Bool <- ($$false)%kami_expr ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET addr : Bit AddrSz (* non-call varbinding *) <- (#d2e @% "addr") ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;

               LET memrq : MemRq (* non-call varbinding *) <- STRUCT { "addr" ::= (#addr) ; "data" ::= (#val1) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 0))  }%kami_expr ;
               BKCall unused : Bit DataSz (* actionBinding *) <- mem'doMem ((#memrq) : MemRq) ;
        Retv ) (* rule executeStore *)
    with Rule instancePrefix--"executeToHost" :=
    (
        Read d2eFifo_valid_v : Bool <- d2eFifo_valid ;
        Read sbFlags_v : Array NumRegs Bool <- sbFlags ;
        Read d2eFifo_reg_v : D2E <- d2eFifo_reg ;
               LET d2e : D2E (* non-call varbinding *) <- #d2eFifo_reg_v ;

        Assert(((((#d2e @% "op") == $$ (* isConstT *)opTh) && (!(#sbFlags_v @[ (#d2e @% "src1") ]))) && #d2eFifo_valid_v)) ;
               Write d2eFifo_valid : Bool <- ($$false)%kami_expr ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET addr : Bit AddrSz (* non-call varbinding *) <- (#d2e @% "addr") ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;

               BKCall unused : Void (* actionBinding *) <- toHost'toHost ((#val1) : Bit DataSz) ;
        Retv ) (* rule executeToHost *)
    }). (* mkDecExecSep *)

    Hint Unfold mkDecExecSepModule : ModuleDefs.
(* Module mkDecExecSep type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkDecExecSep := Build_Empty mkDecExecSepModule.
    Hint Unfold mkDecExecSep : ModuleDefs.
    Hint Unfold mkDecExecSepModule : ModuleDefs.

    End Section'mkDecExecSep.
End module'mkDecExecSep.

Definition mkDecExecSep := module'mkDecExecSep.mkDecExecSep.
Hint Unfold mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSepModule : ModuleDefs.

