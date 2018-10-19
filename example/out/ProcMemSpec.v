Require Import Bool String List Arith.
Require Import Omega.
Require Import micromega.Lia.
Require Import Kami.
Require Import Lib.Indexer.
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

Definition opArith : ConstT (Bit 2) := ($$(natToWord 2 0))%kami.

Definition opLd : ConstT (Bit 2) := ($$(natToWord 2 1))%kami.

Definition opSt : ConstT (Bit 2) := ($$(natToWord 2 2))%kami.

Definition opTh : ConstT (Bit 2) := ($$(natToWord 2 3))%kami.

Definition OpK := Bit 2.

Definition opArithAdd : ConstT (Bit 2) := ($$(natToWord 2 0))%kami.

Definition opArithSub : ConstT (Bit 2) := ($$(natToWord 2 1))%kami.

Definition opArithMul : ConstT (Bit 2) := ($$(natToWord 2 2))%kami.

Definition opArithDiv : ConstT (Bit 2) := ($$(natToWord 2 3))%kami.

Definition OpArithK := Bit 2.

(* * interface Decoder *)
Record Decoder := {
    Decoder'modules: Modules;
    Decoder'isOp : string;
    Decoder'getOp : string;
    Decoder'getArithOp : string;
    Decoder'getSrc1 : string;
    Decoder'getSrc2 : string;
    Decoder'getDst : string;
    Decoder'getAddr : string;
}.

Hint Unfold Decoder'modules : ModuleDefs.
Hint Unfold Decoder'isOp : ModuleDefs.
Hint Unfold Decoder'getOp : ModuleDefs.
Hint Unfold Decoder'getArithOp : ModuleDefs.
Hint Unfold Decoder'getSrc1 : ModuleDefs.
Hint Unfold Decoder'getSrc2 : ModuleDefs.
Hint Unfold Decoder'getDst : ModuleDefs.
Hint Unfold Decoder'getAddr : ModuleDefs.

(* * interface Executer *)
Record Executer := {
    Executer'modules: Modules;
    Executer'execArith : string;
}.

Hint Unfold Executer'modules : ModuleDefs.
Hint Unfold Executer'execArith : ModuleDefs.

Definition MemRqFields := (STRUCT {
    "addr" :: Bit AddrSz;
    "data" :: Bit DataSz;
    "isLoad" :: Bit 1}).
Definition MemRq  := Struct (MemRqFields).

(* * interface ProcRegFile *)
Record ProcRegFile := {
    ProcRegFile'modules: Modules;
    ProcRegFile'sub : string;
    ProcRegFile'upd : string;
}.

Hint Unfold ProcRegFile'modules : ModuleDefs.
Hint Unfold ProcRegFile'sub : ModuleDefs.
Hint Unfold ProcRegFile'upd : ModuleDefs.

Module module'mkProcRegFile.
    Section Section'mkProcRegFile.
    Variable instancePrefix: string.
    Definition mkProcRegFileModule: Modules :=
         (BKMODULE {
        Method instancePrefix--"sub" (idx : (Bit AddrSz)) : Bit DataSz :=
    (
        Ret $0    )

    with Method instancePrefix--"upd" (idx : (Bit AddrSz)) (v : (Bit DataSz)) : Void :=
    (
        Retv    )

    }). (* mkProcRegFile *)

(* Module mkProcRegFile type Module#(ProcRegFile) return type ProcRegFile *)
    Definition mkProcRegFile := Build_ProcRegFile mkProcRegFileModule%kami (instancePrefix--"sub") (instancePrefix--"upd").
    End Section'mkProcRegFile.
End module'mkProcRegFile.

Definition mkProcRegFile := module'mkProcRegFile.mkProcRegFile.
Hint Unfold mkProcRegFile : ModuleDefs.
Hint Unfold module'mkProcRegFile.mkProcRegFile : ModuleDefs.
Hint Unfold module'mkProcRegFile.mkProcRegFileModule : ModuleDefs.

(* * interface Memory *)
Record Memory := {
    Memory'modules: Modules;
    Memory'doMem : string;
}.

Hint Unfold Memory'modules : ModuleDefs.
Hint Unfold Memory'doMem : ModuleDefs.

Module module'mkMemory.
    Section Section'mkMemory.
    Variable instancePrefix: string.
        (* method bindings *)
    (* method binding *) Let mem := mkProcRegFile (instancePrefix--"mem").
    (* instance methods *)
    Let memsub : string := (ProcRegFile'sub mem).
    Let memupd : string := (ProcRegFile'upd mem).
    Definition mkMemoryModule: Modules :=
         (BKMODULE {
        (BKMod (ProcRegFile'modules mem :: nil))
    with Method instancePrefix--"doMem" (req : MemRq) : (Bit DataSz) :=
    (
        If ((#req ! MemRqFields @. "isLoad") == $$(natToWord 1 1)) then (
        
        LET addr : Bit AddrSz <- (#req ! MemRqFields @. "addr");
        CallM ldval : Bit DataSz (* varbinding *) <-  memsub (#addr : Bit AddrSz);
                Ret #ldval
        ) else (
        
        LET addr : Bit AddrSz <- (#req ! MemRqFields @. "addr");
                LET newval : Bit DataSz <- (#req ! MemRqFields @. "data");
                CallM unused : Void (* actionBinding *) <- memupd (#addr : Bit AddrSz) (#newval : Bit DataSz);
        CallM placeholder : Bit DataSz (* varbinding *) <-  memsub (#addr : Bit AddrSz);
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
    ToHost'modules: Modules;
    ToHost'toHost : string;
}.

Hint Unfold ToHost'modules : ModuleDefs.
Hint Unfold ToHost'toHost : ModuleDefs.

Module module'procSpec.
    Section Section'procSpec.
    Variable instancePrefix: string.
    Variable pgm: RegFile.
    Variable dec: Decoder.
    Variable exec: Executer.
    Variable tohost: ToHost.
        (* method bindings *)
    (* method binding *) Let pc := mkReg (Bit PgmSz) (instancePrefix--"pc") ($0)%bk.
    (* method binding *) Let rf := mkRegFileFull (Bit RegFileSz) (Bit DataSz) (instancePrefix--"rf").
    (* method binding *) Let mem := mkMemory (instancePrefix--"mem").
    (* method binding *) Let pc_read : string := (Reg'_read pc).
    (* method binding *) Let pc_write : string := (Reg'_write pc).
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
    Definition procSpecModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules pc :: nil))
    with (BKMod (RegFile'modules rf :: nil))
    with (BKMod (Memory'modules mem :: nil))
    with Rule instancePrefix--"doArith" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call0 : Bool <-  decisOp (#inst : Bit InstrSz) ($$opArith : OpK);

        Assert(#call0);
       CallM op : OpK (* varbinding *) <-  decgetOp (#inst : Bit InstrSz);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM src2 : Bit RegFileSz (* varbinding *) <-  decgetSrc2 (#inst : Bit InstrSz);
       CallM dst : Bit RegFileSz (* varbinding *) <-  decgetDst (#inst : Bit InstrSz);
       CallM val1 : Bit DataSz (* varbinding *) <-  rfsub (#src1 : Bit RegFileSz);
       CallM val2 : Bit DataSz (* varbinding *) <-  rfsub (#src2 : Bit RegFileSz);
       CallM dval : Bit DataSz (* varbinding *) <-  execexecArith (#op : OpArithK) (#val1 : Bit DataSz) (#val2 : Bit DataSz);
               CallM unused : Void (* actionBinding *) <- rfupd (#dst : Bit RegFileSz) (#dval : Bit DataSz);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule doArith *)
    with Rule instancePrefix--"doLoad" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call1 : Bool <-  decisOp (#inst : Bit InstrSz) ($$opLd : OpK);

        Assert(#call1);
       CallM addr : Bit AddrSz (* varbinding *) <-  decgetAddr (#inst : Bit InstrSz);
       CallM dst : Bit RegFileSz (* varbinding *) <-  decgetDst (#inst : Bit InstrSz);
               CallM val : Bit DataSz (* actionBinding *) <- memdoMem (STRUCT { "addr" ::= (#addr); "data" ::= ($0); "isLoad" ::= ($$(natToWord 1 1))  }%kami_expr : MemRq);
       CallM call2 : Void <-  rfupd (#dst : Bit RegFileSz) (#val : Bit DataSz);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule doLoad *)
    with Rule instancePrefix--"doStore" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call3 : Bool <-  decisOp (#inst : Bit InstrSz) ($$opSt : OpK);

        Assert(#call3);
       CallM addr : Bit AddrSz (* varbinding *) <-  decgetAddr (#inst : Bit InstrSz);
       CallM src : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM val : Bit DataSz (* varbinding *) <-  rfsub (#src : Bit RegFileSz);
               CallM unused : Bit DataSz (* actionBinding *) <- memdoMem (STRUCT { "addr" ::= (#addr); "data" ::= (#val); "isLoad" ::= ($$(natToWord 1 0))  }%kami_expr : MemRq);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
        Retv ) (* rule doStore *)
    with Rule instancePrefix--"doHost" :=
    (
        CallM pc_v : Bit PgmSz (* regRead *) <- pc_read();
       CallM inst : Bit InstrSz (* varbinding *) <-  pgmsub (#pc_v : Bit PgmSz);
       CallM call4 : Bool <-  decisOp (#inst : Bit InstrSz) ($$opTh : OpK);

        Assert(#call4);
       CallM src1 : Bit RegFileSz (* varbinding *) <-  decgetSrc1 (#inst : Bit InstrSz);
       CallM val1 : Bit DataSz (* varbinding *) <-  rfsub (#src1 : Bit RegFileSz);
               CallM unused : Void (* actionBinding *) <- tohosttoHost (#val1 : Bit DataSz);
               CallM pc_write ( (#pc_v + $1) : Bit PgmSz );
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

