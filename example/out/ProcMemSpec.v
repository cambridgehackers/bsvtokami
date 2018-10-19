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

Definition RegFileSz := 32.

Definition PgmSz := 16.

Definition opArith : ConstT (Bit 2) := ( (natToWord 2 0))%kami.

Definition opLd : ConstT (Bit 2) := ( (natToWord 2 1))%kami.

Definition opSt : ConstT (Bit 2) := ( (natToWord 2 2))%kami.

Definition opTh : ConstT (Bit 2) := ( (natToWord 2 3))%kami.

Definition OpK := Bit 2.

Definition opArithAdd : ConstT (Bit 2) := ( (natToWord 2 0))%kami.

Definition opArithSub : ConstT (Bit 2) := ( (natToWord 2 1))%kami.

Definition opArithMul : ConstT (Bit 2) := ( (natToWord 2 2))%kami.

Definition opArithDiv : ConstT (Bit 2) := ( (natToWord 2 3))%kami.

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

Definition MemRq := (STRUCT {
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
    Let mem := mkRegFileFull (Bit AddrSz) (Bit DataSz) (instancePrefix--"mem").
    (* instance methods *)
    Let memsub : string := (RegFile'sub mem).
    Let memupd : string := (RegFile'upd mem).
    Local Open Scope kami_expr.

    Definition mkMemoryModule: Mod :=
         (BKMODULE {
        (BKMod (RegFile'mod mem :: nil))
    with Method (instancePrefix--"doMem") (req : MemRq) : (Bit DataSz) :=
    (
        If ((#req @% "isLoad") == $$ (natToWord 1 1)) then (
        
        LET addr : Bit AddrSz <- (#req @% "addr") ;
        Call ldval : Bit DataSz (* varbinding *) <-  memsub ((#addr) : Bit AddrSz) ;
                Ret #ldval
        ) else (
        
        LET addr : Bit AddrSz <- (#req @% "addr") ;
                LET newval : Bit DataSz <- (#req @% "data") ;
                BKCall unused : Void (* actionBinding *) <- memupd ((#addr) : Bit AddrSz) ((#newval) : Bit DataSz) ;
                Call placeholder : Bit DataSz (* varbinding *) <-  memsub ((#addr) : Bit AddrSz) ;
                Ret #placeholder) as retval
 ;
        Ret #retval    )

    }). (* mkMemory *)

(* Module mkMemory type Module#(Memory) return type Memory *)
    Definition mkMemory := Build_Memory mkMemoryModule%kami (instancePrefix--"doMem").
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
    Let pc := mkReg (instancePrefix--"pc") (natToWord PgmSz 0)%bk.
    Let rf := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"rf").
    Let mem := mkMemory (instancePrefix--"mem").
    Let pc_read : string := (Reg'_read pc).
    Let pc_write : string := (Reg'_write pc).
    (* instance methods *)
    Let decgetAddr : string := (Decoder'getAddr dec).
    Let decgetDst : string := (Decoder'getDst dec).
    Let decgetOp : string := (Decoder'getOp dec).
    Let decgetSrc1 : string := (Decoder'getSrc1 dec).
    Let decgetSrc2 : string := (Decoder'getSrc2 dec).
    Let decisOp : string := (Decoder'isOp dec).
    Let execexecArith : string := (Executer'execArith exec).
    Let memdoMem : string := (Memory'doMem mem).
    Let pgmsub : string := (RegFile'sub pgm).
    Let rfsub : string := (RegFile'sub rf).
    Let rfupd : string := (RegFile'upd rf).
    Let tohosttoHost : string := (ToHost'toHost tohost).
    Local Open Scope kami_expr.

    Definition procSpecModule: Mod :=
         (BKMODULE {
        (BKMod (Reg'mod pc :: nil))
    with (BKMod (RegFile'mod rf :: nil))
    with (BKMod (Memory'mod mem :: nil))
    with Rule instancePrefix--"doArith" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call0 : Bool <-  decisOp ((#inst) : Bit InstrSz) ($$ opArith : Bit 2) ;

        Assert (#call0 ) ;
       Call op : OpK (* varbinding *) <-  decgetOp ((#inst) : Bit InstrSz) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 ((#inst) : Bit InstrSz) ;
       Call dst : Bit RegFileSz (* varbinding *) <-  decgetDst ((#inst) : Bit InstrSz) ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfsub ((#src1) : Bit RegFileSz) ;
       Call val2 : Bit DataSz (* varbinding *) <-  rfsub ((#src2) : Bit RegFileSz) ;
       BKCall dval : Bit DataSz (* varbinding *) <-  execexecArith ((#op) : OpArithK) ((#val1) : Bit DataSz) ((#val2) : Bit DataSz) ;
               BKCall unused : Void (* actionBinding *) <- rfupd ((#dst) : Bit RegFileSz) ((#dval) : Bit DataSz) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule doArith *)
    with Rule instancePrefix--"doLoad" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call1 : Bool <-  decisOp ((#inst) : Bit InstrSz) (($$opLd) : OpK) ;

        Assert(#call1) ;
       Call addr : Bit AddrSz (* varbinding *) <-  decgetAddr ((#inst) : Bit InstrSz) ;
       Call dst : Bit RegFileSz (* varbinding *) <-  decgetDst ((#inst) : Bit InstrSz) ;
               Call val : Bit DataSz (* actionBinding *) <- memdoMem ((STRUCT { "addr" ::= (#addr) ; "data" ::= ($0) ; "isLoad" ::= ($$ (natToWord 1 1))  }%kami_expr) : MemRq) ;
       BKCall call2 : Void <-  rfupd ((#dst) : Bit RegFileSz) ((#val) : Bit DataSz) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule doLoad *)
    with Rule instancePrefix--"doStore" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call3 : Bool <-  decisOp ((#inst) : Bit InstrSz) (($$opSt) : OpK) ;

        Assert(#call3) ;
       Call addr : Bit AddrSz (* varbinding *) <-  decgetAddr ((#inst) : Bit InstrSz) ;
       Call src : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call val : Bit DataSz (* varbinding *) <-  rfsub ((#src) : Bit RegFileSz) ;
               Call unused : Bit DataSz (* actionBinding *) <- memdoMem ((STRUCT { "addr" ::= (#addr) ; "data" ::= (#val) ; "isLoad" ::= ($$ (natToWord 1 0))  }%kami_expr) : MemRq) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule doStore *)
    with Rule instancePrefix--"doHost" :=
    (
        Call pc_v : Bit PgmSz (* regRead *) <- pc_read() ;
       Call inst : Bit InstrSz (* varbinding *) <-  pgmsub ((#pc_v) : Bit PgmSz) ;
       BKCall call4 : Bool <-  decisOp ((#inst) : Bit InstrSz) (($$opTh) : OpK) ;

        Assert(#call4) ;
       Call src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 ((#inst) : Bit InstrSz) ;
       Call val1 : Bit DataSz (* varbinding *) <-  rfsub ((#src1) : Bit RegFileSz) ;
               Call unused : Void (* actionBinding *) <- tohosttoHost ((#val1) : Bit DataSz) ;
               Call pc_write ( ((#pc_v + $1)) : Bit PgmSz ) ;
        Retv ) (* rule doHost *)
    }). (* procSpec *)

(* Module procSpec type RegFile#(Bit#(PgmSz), Bit#(InstrSz)) -> Decoder -> Executer -> ToHost -> Module#(Empty) return type Decoder *)
    Definition procSpec := Build_Empty procSpecModule%kami.
    End Section'procSpec.
End module'procSpec.

Definition procSpec := module'procSpec.procSpec.
Hint Unfold procSpec : ModuleDefs.
Hint Unfold module'procSpec.procSpec : ModuleDefs.
Hint Unfold module'procSpec.procSpecModule : ModuleDefs.

