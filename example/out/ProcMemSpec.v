Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import RegFile.
Definition DataSz := 32.

Definition AddrSz := 32.

Definition InstrSz := 32.

Definition NumRegs := 32.

Definition RegFileSz := Nat.log2 NumRegs.

Definition NumInstrs := 8.

Definition PgmSz := Nat.log2 NumInstrs.

Definition opArith : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 0))%kami.

Definition opLd : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 1))%kami.

Definition opSt : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 2))%kami.

Definition opTh : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 3))%kami.

Definition OpK := Bit 2.

Definition opArithAdd : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 0))%kami.

Definition opArithSub : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 1))%kami.

Definition opArithMul : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 2))%kami.

Definition opArithDiv : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 3))%kami.

Definition OpArithK := Bit 2.

(* * interface Decoder *)
Record Decoder := {
    Decoder'mod: Mod;
    Decoder'isOp : string;
    Decoder'getOp : string;
    Decoder'getArithOp : string;
    Decoder'getSrc1 : string;
    Decoder'getSrc2 : string;
    Decoder'getDst : string;
    Decoder'getAddr : string;
}.

Hint Unfold Decoder'mod : ModuleDefs.
Hint Unfold Decoder'isOp : ModuleDefs.
Hint Unfold Decoder'getOp : ModuleDefs.
Hint Unfold Decoder'getArithOp : ModuleDefs.
Hint Unfold Decoder'getSrc1 : ModuleDefs.
Hint Unfold Decoder'getSrc2 : ModuleDefs.
Hint Unfold Decoder'getDst : ModuleDefs.
Hint Unfold Decoder'getAddr : ModuleDefs.

(* * interface Executer *)
Record Executer := {
    Executer'mod: Mod;
    Executer'execArith : string;
}.

Hint Unfold Executer'mod : ModuleDefs.
Hint Unfold Executer'execArith : ModuleDefs.

Definition MemRq := (STRUCT_TYPE {
    "addr" :: Bit AddrSz;
    "data" :: Bit DataSz;
    "isLoad" :: Bit 1}).

(* * interface Memory *)
Record Memory := {
    Memory'mod: Mod;
    Memory'doMem : string;
}.

Hint Unfold Memory'mod : ModuleDefs.
Hint Unfold Memory'doMem : ModuleDefs.

Module module'mkMemory.
    Section Section'mkMemory.
    Variable instancePrefix: string.
        (* method bindings *)
    Let (* action binding *) mem := mkRegFileFull (Bit AddrSz) (Bit DataSz) (instancePrefix--"mem").
    (* instance methods *)
    Let mem'sub : string := (RegFile'sub mem).
    Let mem'upd : string := (RegFile'upd mem).
    Local Open Scope kami_expr.

    Definition mkMemoryModule: Mod :=
         (BKMODULE {
        (BKMod (RegFile'mod mem :: nil))
    with Method (instancePrefix--"doMem") (req : MemRq) : (Bit DataSz) :=
    (
        If ((#req @% "isLoad") == $$ (* intwidth *) (natToWord 1 1)) then (
        
        LET addr : Bit AddrSz (* non-call varbinding *) <- (#req @% "addr") ;
        BKCall ldval : Bit DataSz (* varbinding *) <-  (* translateCall *) mem'sub ((#addr) : Bit AddrSz)  ;
                Ret #ldval
        ) else (
        
        LET addr : Bit AddrSz (* non-call varbinding *) <- (#req @% "addr") ;
                LET newval : Bit DataSz (* non-call varbinding *) <- (#req @% "data") ;
        (* call expr ./ProcMemSpec.bsv:63 *) BKCall call0 : Void <-  (* translateCall *) mem'upd ((#addr) : Bit AddrSz) ((#newval) : Bit DataSz)  ;
        BKCall placeholder : Bit DataSz (* varbinding *) <-  (* translateCall *) mem'sub ((#addr) : Bit AddrSz)  ;
                Ret #placeholder) as retval
 ;
        Ret #retval    )

    }). (* mkMemory *)

    Hint Unfold mkMemoryModule : ModuleDefs.
(* Module mkMemory type Module#(Memory) return type Memory *)
    Definition mkMemory := Build_Memory mkMemoryModule (instancePrefix--"doMem").
    Hint Unfold mkMemory : ModuleDefs.
    Hint Unfold mkMemoryModule : ModuleDefs.

    End Section'mkMemory.
End module'mkMemory.

Definition mkMemory := module'mkMemory.mkMemory.
Hint Unfold mkMemory : ModuleDefs.
Hint Unfold module'mkMemory.mkMemory : ModuleDefs.
Hint Unfold module'mkMemory.mkMemoryModule : ModuleDefs.

(* * interface ToHost *)
Record ToHost := {
    ToHost'mod: Mod;
    ToHost'toHost : string;
}.

Hint Unfold ToHost'mod : ModuleDefs.
Hint Unfold ToHost'toHost : ModuleDefs.

Module module'procSpec.
    Section Section'procSpec.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable tohost: ToHost.
        (* method bindings *)
    Let pc : string := instancePrefix--"pc".
    Let (* action binding *) rf := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"rf").
    Let stage : string := instancePrefix--"stage".
    Let d2e_op : string := instancePrefix--"d2e_op".
    Let d2e_arithOp : string := instancePrefix--"d2e_arithOp".
    Let d2e_src1 : string := instancePrefix--"d2e_src1".
    Let d2e_src2 : string := instancePrefix--"d2e_src2".
    Let d2e_dst : string := instancePrefix--"d2e_dst".
    Let d2e_addr : string := instancePrefix--"d2e_addr".
    Let e2w_dst : string := instancePrefix--"e2w_dst".
    Let e2w_val : string := instancePrefix--"e2w_val".
    (* instance methods *)
    Let dec'getDst : string := (Decoder'getDst dec).
    Let dec'getOp : string := (Decoder'getOp dec).
    Let dec'getSrc1 : string := (Decoder'getSrc1 dec).
    Let dec'getSrc2 : string := (Decoder'getSrc2 dec).
    Let exec'execArith : string := (Executer'execArith exec).
    Let pgm'sub : string := (RegFile'sub pgm).
    Let rf'sub : string := (RegFile'sub rf).
    Let rf'upd : string := (RegFile'upd rf).
    Local Open Scope kami_expr.

    Definition procSpecModule: Mod :=
         (BKMODULE {
        Register pc : Bit PgmSz <- Default
    with (BKMod (RegFile'mod rf :: nil))
    with Register stage : Bit 2 <- Default
    with Register d2e_op : OpK <- Default
    with Register d2e_arithOp : OpArithK <- Default
    with Register d2e_src1 : Bit RegFileSz <- Default
    with Register d2e_src2 : Bit RegFileSz <- Default
    with Register d2e_dst : Bit RegFileSz <- Default
    with Register d2e_addr : Bit AddrSz <- Default
    with Register e2w_dst : Bit RegFileSz <- Default
    with Register e2w_val : Bit DataSz <- Default
    with Rule instancePrefix--"doDecode" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
        Read stage_v : Bit 2 <- stage ;

        Assert((#stage_v == $$ (* intwidth *) (natToWord 2 0))) ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz)  ;
       (* call expr ./ProcMemSpec.bsv:95 *) BKCall call1 : OpK <-  (* translateCall *) dec'getOp ((#inst) : Bit InstrSz)  ;
               Write d2e_op : OpK <- #call1  ;
       (* call expr ./ProcMemSpec.bsv:96 *) BKCall call2 : Bit RegFileSz <-  (* translateCall *) dec'getSrc1 ((#inst) : Bit InstrSz)  ;
               Write d2e_src1 : Bit RegFileSz <- #call2  ;
       (* call expr ./ProcMemSpec.bsv:97 *) BKCall call3 : Bit RegFileSz <-  (* translateCall *) dec'getSrc2 ((#inst) : Bit InstrSz)  ;
               Write d2e_src2 : Bit RegFileSz <- #call3  ;
       (* call expr ./ProcMemSpec.bsv:98 *) BKCall call4 : Bit RegFileSz <-  (* translateCall *) dec'getDst ((#inst) : Bit InstrSz)  ;
               Write d2e_dst : Bit RegFileSz <- #call4  ;
               Write stage : Bit 2 <- $$ (* intwidth *) (natToWord 2 1)  ;
        Retv ) (* rule doDecode *)
    with Rule instancePrefix--"doExec" :=
    (
        Read d2e_dst_v : Bit RegFileSz <- d2e_dst ;
        Read d2e_op_v : OpK <- d2e_op ;
        Read d2e_src1_v : Bit RegFileSz <- d2e_src1 ;
        Read d2e_src2_v : Bit RegFileSz <- d2e_src2 ;
        Read stage_v : Bit 2 <- stage ;

        Assert((#stage_v == $$ (* intwidth *) (natToWord 2 1))) ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#d2e_src1_v) : Bit RegFileSz)  ;
       BKCall val2 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#d2e_src2_v) : Bit RegFileSz)  ;
       BKCall dval : Bit DataSz (* varbinding *) <-  (* translateCall *) exec'execArith ((#d2e_op_v) : OpArithK) ((#val1) : Bit DataSz) ((#val2) : Bit DataSz)  ;
               Write e2w_dst : Bit RegFileSz <- #d2e_dst_v  ;
               Write e2w_val : Bit DataSz <- #dval  ;
               Write stage : Bit 2 <- $$ (* intwidth *) (natToWord 2 2)  ;
        Retv ) (* rule doExec *)
    with Rule instancePrefix--"doWriteBack" :=
    (
        Read e2w_dst_v : Bit RegFileSz <- e2w_dst ;
        Read e2w_val_v : Bit DataSz <- e2w_val ;
        Read pc_v : Bit PgmSz <- pc ;
        Read stage_v : Bit 2 <- stage ;

        Assert((#stage_v == $$ (* intwidth *) (natToWord 2 2))) ;
       (* call expr ./ProcMemSpec.bsv:117 *) BKCall call5 : Void <-  (* translateCall *) rf'upd ((#e2w_dst_v) : Bit RegFileSz) ((#e2w_val_v) : Bit DataSz)  ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord _ 1))  ;
               Write stage : Bit 2 <- $$ (* intwidth *) (natToWord 2 0)  ;
        Retv ) (* rule doWriteBack *)
    }). (* procSpec *)

    Hint Unfold procSpecModule : ModuleDefs.
(* Module procSpec type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition procSpec := Build_Empty procSpecModule.
    Hint Unfold procSpec : ModuleDefs.
    Hint Unfold procSpecModule : ModuleDefs.

    End Section'procSpec.
End module'procSpec.

Definition procSpec := module'procSpec.procSpec.
Hint Unfold procSpec : ModuleDefs.
Hint Unfold module'procSpec.procSpec : ModuleDefs.
Hint Unfold module'procSpec.procSpecModule : ModuleDefs.

