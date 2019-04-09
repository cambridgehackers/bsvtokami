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


Module module'mkMultiCycleProc.
    Section Section'mkMultiCycleProc.
    Variable instancePrefix: string.
    Variable dec: Decoder.Decoder.
    Variable exec: Decoder.Executer.
        (* method bindings *)
    Let rf: string := instancePrefix--"rf".
    Let mem: string := instancePrefix--"mem".
    Let pgm: string := "pgm".
    Let toHost: string := instancePrefix--"th".
    Let decoder_addr    : string := instancePrefix--"decoder_addr".
    Let decoder_arithOp : string := instancePrefix--"decoder_arithOp".
    Let decoder_op      : string := instancePrefix--"decoder_op".
    Let decoder_pc      : string := instancePrefix--"decoder_pc".
    Let decoder_dst     : string := instancePrefix--"decoder_dst".
    Let decoder_src1    : string := instancePrefix--"decoder_src1".
    Let decoder_src2    : string := instancePrefix--"decoder_src2".
    Let exec_dst : string := instancePrefix--"exec_dst".
    Let exec_val : string := instancePrefix--"exec_val".
    Let refproc_state : string := instancePrefix--"refproc_state".
    (* instance methods *)
    Let mem'doMem : string := mem--"doMem".
    Let toHost'toHost : string := toHost--"toHost".
    Local Open Scope kami_expr.

    Definition mkMultiCycleProcModule: Mod :=
         (BKMODULE {

         Register decoder_pc : Bit PgmSz <-  Default

    with Register decoder_addr    : Bit AddrSz <- Default
    with Register decoder_arithOp : OpArithK <- Default
    with Register decoder_op      : OpK <- Default
    with Register decoder_dst     : Bit RegFileSz <- Default
    with Register decoder_src1    : Bit RegFileSz <- Default
    with Register decoder_src2    : Bit RegFileSz <- Default

    with Register exec_dst : Bit RegFileSz <- Default
    with Register exec_val : Bit DataSz <- Default
    with Register refproc_state : Bit 2 <- Default
    with Register pgm : Array NumInstrs (Bit InstrSz) <- Default
    with Register rf : Array NumRegs (Bit DataSz) <- Default

    with Rule instancePrefix--"decode" :=
    (
        Read decoder_pc_v : Bit PgmSz <- decoder_pc ;

        Read refproc_state_v : Bit 2 <- refproc_state ;
        Assert(#refproc_state_v == $$(natToWord 2 0)) ;
       Read instrs : Array NumInstrs (Bit InstrSz) <- pgm ;
       LET inst : Bit InstrSz <- #instrs @[ #decoder_pc_v ] ;
       LET op : OpK (* varbinding *) <-  getOp dec _ inst ;
       LET arithOp : OpArithK (* varbinding *) <-  getArithOp dec _ inst ;
       LET src1 : Bit RegFileSz (* varbinding *) <-  getSrc1 dec _ inst ;
       LET src2 : Bit RegFileSz (* varbinding *) <-  getSrc2 dec _ inst ;
       LET dst : Bit RegFileSz (* varbinding *) <-  getDst dec _ inst ;
       LET addr : Bit AddrSz (* varbinding *) <- getAddr dec _ inst ;
               Write decoder_addr    : Bit AddrSz    <- #addr ;
               Write decoder_arithOp : OpArithK      <- #arithOp ;
               Write decoder_op      : OpK           <- #op ;
               Write decoder_dst     : Bit RegFileSz <- #dst ;
               Write decoder_src1    : Bit RegFileSz <- #src1 ;
               Write decoder_src2    : Bit RegFileSz <- #src2 ;
               Write refproc_state : Bit 2 <- ($$(natToWord 2 1))%kami_expr ;
               Write decoder_pc : Bit PgmSz <- (#decoder_pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule decode *)

    with Rule instancePrefix--"executeArith" :=
    (
        Read refproc_state_v : Bit 2 <- refproc_state ;

        Read decoder_addr_v    : Bit AddrSz    <- decoder_addr ;
        Read decoder_arithOp_v : OpArithK      <- decoder_arithOp ;
        Read decoder_op_v      : OpK           <- decoder_op ;
        Read decoder_dst_v     : Bit RegFileSz <- decoder_dst ;
        Read decoder_src1_v    : Bit RegFileSz <- decoder_src1 ;
        Read decoder_src2_v    : Bit RegFileSz <- decoder_src2 ;

        Assert( #decoder_op_v == $$ (* isConstT *)opArith
	       && (#refproc_state_v == $$(natToWord 2 1)))  ;
       LET src1 : Bit RegFileSz (* non-call varbinding *) <- #decoder_src1_v ;
       LET src2 : Bit RegFileSz (* non-call varbinding *) <- #decoder_src2_v ;
       LET dst : Bit RegFileSz (* non-call varbinding *) <- #decoder_dst_v ;
       LET arithOp : OpArithK (* non-call varbinding *) <- #decoder_arithOp_v ;

       Read regsval : Array NumRegs (Bit DataSz) <- rf ;
       LET val1 : Bit DataSz (* varbinding *) <-  #regsval @[ #src1 ] ;
       LET val2 : Bit DataSz (* varbinding *) <-  #regsval @[ #src2 ] ;

       LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2) ;
       (* LET flags : Array NumRegs Bool (* non-call varbinding *) <- #sbFlags_v ;
       LET flags : Array NumRegs Bool <- #flags @[#dst <- $$true ] ;
       Write sbFlags : Array NumRegs Bool <- #flags ; *)
       Write exec_dst : Bit RegFileSz <- #dst ;
       Write exec_val : Bit DataSz <- #execVal ;
       Write refproc_state : Bit 2 <- ($$(natToWord 2 2))%kami_expr ;
       Retv ) (* rule executeArith *)

    with Rule instancePrefix--"writeback" :=
    (
        Read refproc_state_v : Bit 2 <- refproc_state ;

        Assert(#refproc_state_v == $$(natToWord 2 2)) ;
       Read rf_v : Array NumRegs (Bit DataSz) <- rf ;
       Read exec_dst_v : Bit RegFileSz <- exec_dst ;
       Read exec_val_v : Bit DataSz <- exec_val ;
       LET rf_v : Array NumRegs (Bit DataSz) <- #rf_v @[ #exec_dst_v <- #exec_val_v ] ;
       Write rf : Array NumRegs (Bit DataSz)  <- #rf_v ;
       Write refproc_state : Bit 2 <- ($$(natToWord 2 0))%kami_expr ;
        Retv ) (* rule writeback *)

    }). (* mkMultiCycleProc *)

    Close Scope kami_expr.

    Hint Unfold mkMultiCycleProcModule : ModuleDefs.
(* Module mkMultiCycleProc type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ProcRegs -> Memory -> ToHost -> Module#(Empty) return type Decoder *)
    Definition mkMultiCycleProc := Build_Empty mkMultiCycleProcModule.
    Hint Unfold mkMultiCycleProc : ModuleDefs.
    Hint Unfold mkMultiCycleProcModule : ModuleDefs.

    End Section'mkMultiCycleProc.
End module'mkMultiCycleProc.

Definition mkMultiCycleProc := module'mkMultiCycleProc.mkMultiCycleProc.
Hint Unfold mkMultiCycleProc : ModuleDefs.
Hint Unfold module'mkMultiCycleProc.mkMultiCycleProc : ModuleDefs.
Hint Unfold module'mkMultiCycleProc.mkMultiCycleProcModule : ModuleDefs.

