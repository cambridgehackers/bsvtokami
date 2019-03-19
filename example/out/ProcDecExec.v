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
    Variable dec: Decoder.Decoder.
    Variable exec: Decoder.Executer.
        (* method bindings *)
    Let pc : string := instancePrefix--"pc".
    (* Let sbFlags : string := instancePrefix--"sbFlags". *)
    Let rf: string := instancePrefix--"regs".
    Let mem: string := instancePrefix--"mem".
    Let pgm: string := "pgm".
    Let toHost: string := instancePrefix--"th".
    Let e2wFifo_reg: string := instancePrefix--"e2wFifo_reg".
    Let e2wFifo_valid: string := instancePrefix--"e2wFifo_valid".
    (* instance methods *)
    Let mem'doMem : string := mem--"doMem".
    Let toHost'toHost : string := toHost--"toHost".
    Local Open Scope kami_expr.

    Definition mkDecExecModule: Mod :=
         (BKMODULE {
    Register e2wFifo_reg : E2W <- Default
    with Register e2wFifo_valid : Bool <- (false)%kami_expr
    with Register pc : Bit PgmSz <- natToWord PgmSz 0
    with Register pgm : Array NumInstrs (Bit InstrSz) <- Default
    with Register rf : Array NumRegs (Bit DataSz) <- Default
    (* with Register sbFlags : Array NumRegs Bool <- Default *)
    with Rule instancePrefix--"decexecArith" :=
    (
        Read e2wFifo_valid_v : Bool <- e2wFifo_valid ;
        Read pc_v : Bit PgmSz <- pc ;
        (* Read sbFlags_v : Array NumRegs Bool <- sbFlags ; *)
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET inst : Bit InstrSz <- #instrs @[  #pc_v ] ;
       LET isOpArith : Bool <- (getOp dec _ inst) == $$opArith ;
       LET src1 : Bit RegFileSz <-  getSrc1 dec _ inst ;
       LET src2 : Bit RegFileSz <-  getSrc2 dec _ inst ;

        Assert(#isOpArith 
	(* && !(#sbFlags_v @[ #src1 ]) *)
	(* && (!(#sbFlags_v @[ #src2 ])) *)
	 && (!#e2wFifo_valid_v)) ;
       LET dst : Bit RegFileSz (* varbinding *) <-  getDst dec _ inst ;
       LET arithOp : OpArithK (* varbinding *) <- getArithOp dec _ inst ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;
       LET val2 : Bit DataSz (* varbinding *) <-  #regsval @[ #src2 ] ;
       LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2) ;
       (* LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
               LET flags : Array NumRegs Bool <- #flags @[#dst <- $$true] ;
               Write sbFlags : Array NumRegs Bool <- #flags ; *)
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               Write e2wFifo_reg : E2W <- #e2w ;
               Write e2wFifo_valid : Bool <- ($$true)%kami_expr ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decexecArith *)
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
    Variable dec: Decoder.Decoder.
    Variable exec: Decoder.Executer.
        (* method bindings *)
    Let rf: string := instancePrefix--"regs".
    Let mem: string := instancePrefix--"mem".
    Let pgm: string := "pgm".
    Let toHost: string := instancePrefix--"th".
    Let d2eFifo_reg : string := instancePrefix--"d2eFifo_reg".
    Let d2eFifo_valid : string := instancePrefix--"d2eFifo_valid".
    Let e2wFifo_reg : string := instancePrefix--"e2wFifo_reg".
    Let e2wFifo_valid : string := instancePrefix--"e2wFifo_valid".
    Let decoder_pc : string := instancePrefix--"pc".
    (* Let sbFlags : string := instancePrefix--"sbFlags". *)
    (* instance methods *)
    Let mem'doMem : string := mem--"doMem".
    Let toHost'toHost : string := toHost--"toHost".
    Local Open Scope kami_expr.

    Definition mkDecExecSepModule: Mod :=
         (BKMODULE {
    Register d2eFifo_reg : D2E <- Default
    with Register d2eFifo_valid : Bool <- (false)%kami_expr
    with Register decoder_pc : Bit PgmSz <-  (* intwidth *) (natToWord PgmSz 0)
    with Register e2wFifo_reg : E2W <- Default
    with Register e2wFifo_valid : Bool <- (false)%kami_expr
    with Register pgm : Array NumInstrs (Bit InstrSz) <- Default
    with Register rf : Array NumRegs (Bit DataSz) <- Default
    (* with Register sbFlags : Array NumRegs Bool <- Default *)
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
        (* Read sbFlags_v : Array NumRegs Bool <- sbFlags ; *)
        Read d2eFifo_reg_v : D2E <- d2eFifo_reg ;
               LET d2e : D2E (* non-call varbinding *) <- #d2eFifo_reg_v ;

        Assert( ((#d2e @% "op") == $$ (* isConstT *)opArith)
	      (* && (!(#sbFlags_v @[ (#d2e @% "src1") ])) *)
	      (*  && (!(#sbFlags_v @[ (#d2e @% "src2") ])) *)
	       && #d2eFifo_valid_v && (!#e2wFifo_valid_v)) ;
               Write d2eFifo_valid : Bool <- ($$false)%kami_expr ;
               LET src1 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src1") ;
               LET src2 : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "src2") ;
               LET dst : Bit RegFileSz (* non-call varbinding *) <- (#d2e @% "dst") ;
               LET arithOp : OpArithK (* non-call varbinding *) <- (#d2e @% "arithOp") ;
       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;
       LET val2 : Bit DataSz (* varbinding *) <-  #regsval @[ #src2 ] ;

       LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2) ;
               (* LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
               LET flags : Array NumRegs Bool <- #flags @[#dst <- $$true ] ;
               Write sbFlags : Array NumRegs Bool <- #flags ; *)
               LET e2w : E2W (* non-call varbinding *) <- STRUCT { "idx" ::= (#dst) ; "val" ::= (#execVal)  }%kami_expr ;
               Write e2wFifo_reg : E2W <- #e2w ;
               Write e2wFifo_valid : Bool <- ($$true)%kami_expr ;
        Retv ) (* rule executeArith *)
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

