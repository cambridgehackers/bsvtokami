Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.
Require Import Decoder.
Require Import ProcMemSpec.

Module module'mkMultiCycleProc.
    Section Section'mkMultiCycleProc.
    Variable instancePrefix: string.
    Variable pgm: string.
    Variable dec: string.
    Variable exec: Decoder.Executer.
    Variable mem: string.
        (* method bindings *)
    Let pc : string := instancePrefix--"pc".
    Let state : string := instancePrefix--"state".
    Let d2e_op : string := instancePrefix--"d2e_op".
    Let d2e_arithOp : string := instancePrefix--"d2e_arithOp".
    Let d2e_src1 : string := instancePrefix--"d2e_src1".
    Let d2e_src2 : string := instancePrefix--"d2e_src2".
    Let d2e_dst : string := instancePrefix--"d2e_dst".
    Let d2e_addr : string := instancePrefix--"d2e_addr".
    Let e2w_val : string := instancePrefix--"e2w_val".
    (* instance methods *)
    Let dec'getDst : string := (dec--"getDst").
    Let dec'getOp : string := (dec--"getOp").
    Let dec'getArithOp : string := (dec--"getArithOp").
    Let dec'getAddr : string := (dec--"getAddr").
    Let dec'getSrc1 : string := (dec--"getSrc1").
    Let dec'getSrc2 : string := (dec--"getSrc2").
    Let pgm'sub : string := (pgm--"sub").
    Let init_pc_valid : bool := true.
    Local Open Scope kami_expr.

    Definition mkMultiCycleProcModule: ModWf :=
         (MOD_WF {
        Register (instancePrefix--"pc") : Bit PgmSz <- Default
    with Register (instancePrefix--"state") : Bit 2 <- Default
    with Register (instancePrefix--"rf") : Array NumRegs (Bit DataSz) <- Default
    with Register (instancePrefix--"d2e_op") : Bit 2 <- Default
    with Register (instancePrefix--"d2e_arithOp") : Bit 2 <- Default
    with Register (instancePrefix--"d2e_src1") : Bit RegFileSz <- Default
    with Register (instancePrefix--"d2e_src2") : Bit RegFileSz <- Default
    with Register (instancePrefix--"d2e_dst") : Bit RegFileSz <- Default
    with Register (instancePrefix--"d2e_addr") : Bit AddrSz <- Default
    with Register (instancePrefix--"e2w_dst") : Bit RegFileSz <- Default
    with Register (instancePrefix--"e2w_val") : Bit DataSz <- Default

    with Rule instancePrefix--"doDecode" :=
    (
        Read state_v : Bit 2 <- state ;
        Read pc_v : Bit PgmSz <- pc ;

        Assert(#state_v == $$(natToWord 2 0)) ;
       Call inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz)  ;
       (* call expr ./ProcMemSpec.bsv:95 *) Call call1 : Bit 2 <-  (* translateCall *) dec'getOp ((#inst) : Bit InstrSz)  ;
               Write d2e_op : Bit 2 <- #call1  ;
       (* call expr ./ProcMemSpec.bsv:95 *) Call calloak : Bit 2 <-  (* translateCall *) dec'getArithOp ((#inst) : Bit InstrSz)  ;
               Write d2e_arithOp : Bit 2 <- #calloak  ;
       (* call expr ./ProcMemSpec.bsv:95 *) Call calladdr : Bit AddrSz <-  (* translateCall *) dec'getAddr ((#inst) : Bit InstrSz)  ;
               Write d2e_addr : Bit AddrSz <- #calladdr  ;
       (* call expr ./ProcMemSpec.bsv:96 *) Call call2 : Bit RegFileSz <-  (* translateCall *) dec'getSrc1 ((#inst) : Bit InstrSz)  ;
               Write d2e_src1 <- #call2  ;
       (* call expr ./ProcMemSpec.bsv:97 *) Call call3 : Bit RegFileSz <-  (* translateCall *) dec'getSrc2 ((#inst) : Bit InstrSz)  ;
               Write d2e_src2 : Bit RegFileSz <- #call3  ;
       (* call expr ./ProcMemSpec.bsv:98 *) Call call4 : Bit RegFileSz <-  (* translateCall *) dec'getDst ((#inst) : Bit InstrSz)  ;
               Write d2e_dst : Bit RegFileSz <- #call4  ;
               Write state : Bit 2 <- $$(natToWord 2 1)  ;
        Retv ) (* rule doDecode *)

    with Rule instancePrefix--"doExec" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
        Read d2e_dst_v : Bit RegFileSz <- d2e_dst ;
        Read d2e_arithop_v : Bit 2 <- d2e_arithOp ;
        Read d2e_addr_v : Bit AddrSz <- d2e_addr ;
        Read d2e_op_v : Bit 2 <- d2e_op ;
        Read d2e_src1_v : Bit RegFileSz <- d2e_src1 ;
        Read d2e_src2_v : Bit RegFileSz <- d2e_src2 ;
        Read state_v : Bit 2 <- state ;

        Assert(#state_v == $$(natToWord 2 1)) ;

       Read rf_v : Array NumRegs (Bit DataSz) <- (instancePrefix--"rf") ;
       LET val1 : Bit DataSz (* varbinding *) <-  #rf_v @[#d2e_src1_v]  ;
       LET val2 : Bit DataSz (* varbinding *) <-  #rf_v @[#d2e_src2_v]  ;

       LET eval : ExecuterResult <-  (execArith exec _ d2e_arithop_v val1 val2)  ;

       LET dval : Bit DataSz <- #eval @% "data" ;
       LET addr : Bit AddrSz <- #eval @% "addr" ;
       LET nextpc : Bit PgmSz <- #eval @% "nextpc" ;

               Write instancePrefix--"e2w_dst" : Bit RegFileSz <- #d2e_dst_v  ;
               Write instancePrefix--"e2w_val" : Bit DataSz <- #dval  ;
               Write state : Bit 2 <- $$(natToWord 2 2)  ;

        BKCall unused : Void <- (mem--"req") (#addr : Bit DataSz) ;

        Retv ) (* rule doExec *)

    with Rule instancePrefix--"doWriteBack" :=
    (
        Read e2w_dst_v : Bit RegFileSz <- instancePrefix--"e2w_dst" ;
        Read e2w_val_v : Bit DataSz <- instancePrefix--"e2w_val" ;
        Read pc_v : Bit PgmSz <- pc ;
        Read state_v : Bit 2 <- state ;

        Assert (#state_v == $$(natToWord 2 2)) ;
        Read rf_v : Array NumRegs (Bit DataSz) <- (instancePrefix--"rf") ;
	LET rf_v : Array NumRegs (Bit DataSz) <- #rf_v @[#e2w_dst_v <- #e2w_val_v ]  ;
        Write (instancePrefix--"rf") : Array NumRegs (Bit DataSz) <-  #rf_v ;
        Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1))  ;

        BKCall unused : Bit DataSz <- (mem--"resp") () ;

        Write state : Bit 2 <- $$(natToWord 2 0)  ;

        Retv ) (* rule doWriteBack *)
    }). (* mkMultiCycleProc *)

    Hint Unfold mkMultiCycleProcModule : ModuleDefs.

    Definition mkMultiCycleProc := Build_Empty mkMultiCycleProcModule.
    Hint Unfold mkMultiCycleProc : ModuleDefs.
    Hint Unfold mkMultiCycleProcModule : ModuleDefs.

    End Section'mkMultiCycleProc.
End module'mkMultiCycleProc.

Definition mkMultiCycleProc := module'mkMultiCycleProc.mkMultiCycleProc.
Hint Unfold mkMultiCycleProc : ModuleDefs.
Hint Unfold module'mkMultiCycleProc.mkMultiCycleProc : ModuleDefs.
Hint Unfold module'mkMultiCycleProc.mkMultiCycleProcModule : ModuleDefs.
