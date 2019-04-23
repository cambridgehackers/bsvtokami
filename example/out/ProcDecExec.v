Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import Decoder.
Require Import FIFO.
Require Import RegFile.
Require Import ProcMemSpec.
(* * interface NoMethods *)
Record NoMethods := {
    NoMethods'mod: ModWf;
}.

Hint Unfold NoMethods'mod : ModuleDefs.

Module module'mkDecExec.
    Section Section'mkDecExec.
    Variable instancePrefix: string.
    Variable pgm: string.
    Variable dec: string.
    Variable exec: Decoder.Executer.
    Variable e2wfifo: string.
        (* method bindings *)
    (* instance methods *)
    Local Open Scope kami_expr.

    Definition mkDecExecModule: ModWf :=
         (MOD_WF {
        Register (instancePrefix--"pc") : Bit PgmSz <- Default
    with Register (instancePrefix--"rf") : Array NumRegs (Bit DataSz) <- Default
    with Rule instancePrefix--"decexecArith" :=
    (
        Read pc_v : Bit PgmSz <- (instancePrefix--"pc") ;
        Read rf_v : Array NumRegs (Bit DataSz) <- (instancePrefix--"rf") ;
       BKCall inst : Bit InstrSz <-  (* translateCall *) (pgm--"sub") ((#pc_v) : Bit PgmSz)  ;
       BKCall op : Bit 2 <-  (* translateCall *) (dec--"getOp") ((#inst) : Bit InstrSz)  ;

        Assert(#op == ($$ (* isConstT *)opArith)) ;
       BKCall src1 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) (dec--"getSrc1") ((#inst) : Bit InstrSz)  ;
       BKCall src2 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) (dec--"getSrc2") ((#inst) : Bit InstrSz)  ;
       BKCall dst : Bit RegFileSz (* varbinding *) <-  (* translateCall *) (dec--"getDst") ((#inst) : Bit InstrSz)  ;
       BKCall retval : Bit 2 <- (dec--"getArithOp") ((#inst) : Bit InstrSz)  ;
      LET arithOp : Bit 2 <- #retval ;
      LET val1 : Bit DataSz (* non-call varbinding *) <- (#rf_v @[ #src1 ]) ;
      LET val2 : Bit DataSz (* non-call varbinding *) <- (#rf_v @[ #src2 ]) ;
      LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2)  ;
      BKCall enq : Void (* actionBinding *) <- (e2wfifo--"enq") ((#execVal) : Bit DataSz)  ;
      Write (instancePrefix--"pc") : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1))  ;
      Retv ) (* rule decexecArith *)
    }). (* mkDecExec *)

    Hint Unfold mkDecExecModule : ModuleDefs.

    Definition mkDecExec := Build_NoMethods mkDecExecModule.
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
    Variable dec: string.
    Variable exec: Decoder.Executer.
    Variable e2wfifo: string.
    Local Open Scope kami_expr.

    Definition mkDecExecSepModule: ModWf :=
         (MOD_WF {
    Register (instancePrefix--"pc") : Bit PgmSz <- Default
    with Register (instancePrefix--"d2e_valid")   : Bool <- Default
    with Register (instancePrefix--"d2e_pc")      : Bit PgmSz <- Default
    with Register (instancePrefix--"d2e_op")      : Bit 2 <- Default
    with Register (instancePrefix--"d2e_arithOp") : Bit 2 <- Default
    with Register (instancePrefix--"d2e_src1")    : Bit RegFileSz <- Default
    with Register (instancePrefix--"d2e_src2")    : Bit RegFileSz <- Default
    with Register (instancePrefix--"d2e_dst")     : Bit RegFileSz <- Default
    with Register (instancePrefix--"rf") : Array NumRegs (Bit DataSz) <- Default
    with Rule instancePrefix--"decode" :=
    (
        Read pc_v : Bit PgmSz <- (instancePrefix--"pc") ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) (pgm--"sub") ((#pc_v) : Bit PgmSz)  ;
       BKCall op : Bit 2 (* varbinding *) <-  (* translateCall *) (dec--"getOp") ((#inst) : Bit InstrSz)  ;
       BKCall arithOp : Bit 2 (* varbinding *) <-  (* translateCall *) (dec--"getArithOp") ((#inst) : Bit InstrSz)  ;
       BKCall src1 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) (dec--"getSrc1") ((#inst) : Bit InstrSz)  ;
       BKCall src2 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) (dec--"getSrc2") ((#inst) : Bit InstrSz)  ;
       BKCall dst  : Bit RegFileSz (* varbinding *) <-  (* translateCall *) (dec--"getDst") ((#inst) : Bit InstrSz)  ;
       Write (instancePrefix--"d2e_valid") : Bool <- $$true ;
       Write (instancePrefix--"d2e_pc") : Bit PgmSz <- #pc_v ;
       Write (instancePrefix--"d2e_arithOp") : Bit 2 <- #arithOp ;
       Write (instancePrefix--"d2e_op") : Bit 2 <- #op ;
       Write (instancePrefix--"d2e_src1") : Bit RegFileSz <- #src1 ;
       Write (instancePrefix--"d2e_src2") : Bit RegFileSz <- #src2 ;
       Write (instancePrefix--"d2e_dst") : Bit RegFileSz <- #dst ;
       Write (instancePrefix--"pc") : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1))  ;
        Retv ) (* rule decode *)

    with Rule instancePrefix--"executeArith" :=
    (
        Read rf_v : Array NumRegs (Bit DataSz) <- (instancePrefix--"rf") ;

	Read src1    : Bit RegFileSz <- (instancePrefix--"d2e_src1") ;
	Read src2    : Bit RegFileSz <- (instancePrefix--"d2e_src2") ;
	Read dst     : Bit RegFileSz <- (instancePrefix--"d2e_dst") ;
	Read arithOp : Bit 2 <- (instancePrefix--"d2e_arithOp") ;
	Read op      : Bit 2 <- (instancePrefix--"d2e_op") ;
	Read valid   : Bool <- (instancePrefix--"d2e_valid") ;
        Assert (#op == $$ (* isConstT *)opArith && #valid) ;

	LET val1 : Bit DataSz (* non-call varbinding *) <- (#rf_v @[ #src1 ]) ;
	LET val2 : Bit DataSz (* non-call varbinding *) <- (#rf_v @[ #src2 ]) ;
        LET execVal : Bit DataSz <- (execArith exec _ arithOp val1 val2)  ;
	BKCall enq : Void (* actionBinding *) <- (e2wfifo--"enq") ((#execVal) : Bit DataSz)  ;
        Retv ) (* rule executeArith *)
    }). (* mkDecExecSep *)

    Hint Unfold mkDecExecSepModule : ModuleDefs.

    Definition mkDecExecSep := Build_NoMethods mkDecExecSepModule.
    Hint Unfold mkDecExecSep : ModuleDefs.
    Hint Unfold mkDecExecSepModule : ModuleDefs.

    End Section'mkDecExecSep.
End module'mkDecExecSep.

Definition mkDecExecSep := module'mkDecExecSep.mkDecExecSep.
Hint Unfold mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSep : ModuleDefs.
Hint Unfold module'mkDecExecSep.mkDecExecSepModule : ModuleDefs.
