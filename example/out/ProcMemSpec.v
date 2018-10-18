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
Require Import Vector.
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

(* * interface Decoder#(instsz, rfsz, addrsz) *)
Record Decoder := {
    Decoder'modules: Modules;
    Decoder'getOp : string;
    Decoder'getSrc1 : string;
    Decoder'getSrc2 : string;
    Decoder'getDst : string;
    Decoder'getAddr : string;
}.

Hint Unfold Decoder'modules : ModuleDefs.
Hint Unfold Decoder'getOp : ModuleDefs.
Hint Unfold Decoder'getSrc1 : ModuleDefs.
Hint Unfold Decoder'getSrc2 : ModuleDefs.
Hint Unfold Decoder'getDst : ModuleDefs.
Hint Unfold Decoder'getAddr : ModuleDefs.

(* * interface Executer#(instsz, datasz) *)
Record Executer := {
    Executer'modules: Modules;
    Executer'execArith : string;
}.

Hint Unfold Executer'modules : ModuleDefs.
Hint Unfold Executer'execArith : ModuleDefs.

Definition MemRqFields (addrsz : nat) (datasz : nat) := (STRUCT {
    "addr" :: Bit addrsz;
    "data" :: Bit datasz;
    "isLoad" :: Bit 1}).
Definition MemRq  (addrsz : nat) (datasz : nat) := Struct (MemRqFields addrsz datasz).

(* * interface Memory#(addrsz, datasz) *)
Record Memory := {
    Memory'modules: Modules;
    Memory'doMem : string;
}.

Hint Unfold Memory'modules : ModuleDefs.
Hint Unfold Memory'doMem : ModuleDefs.

Module module'mkMemory.
    Section Section'mkMemory.
    Variable addrsz : nat.
    Variable datasz : nat.
    Variable instancePrefix: string.
        (* method bindings *)
    Let mem := mkRegFileFull (Bit datasz) (Bit addrsz) (instancePrefix--"mem").
    (* instance methods *)
    Let memsub : string := (RegFile'sub mem).
    Let memupd : string := (RegFile'upd mem).
    Definition mkMemoryModule: Modules :=
         (BKMODULE {
        (BKMod (RegFile'modules mem :: nil))
    with Method instancePrefix--"doMem" (req : (MemRq addrsz datasz)) : (Bit datasz) :=
    (
        If ((#req ! (MemRqFields addrsz datasz) @. "isLoad") == $$(natToWord 1 1)) then (
        
        LET addr : Bit addrsz <- (#req ! (MemRqFields addrsz datasz) @. "addr");
        CallM ldval : Bit datasz (* varbinding *) <-  memsub (#addr : Bit addrsz);
                Ret #ldval
        ) else (
        
        LET addr : Bit addrsz <- (#req ! (MemRqFields addrsz datasz) @. "addr");
                LET newval : Bit datasz <- (#req ! (MemRqFields addrsz datasz) @. "data");
                CallM unused : Void (* actionBinding *) <- memupd (#addr : Bit addrsz) (#newval : Bit datasz);
        CallM placeholder : Bit datasz (* varbinding *) <-  memsub (#addr : Bit addrsz);
                Ret #placeholder) as retval
;
        Ret #retval    )

    }). (* mkMemory *)

(* Module mkMemory type Module#(Memory#(addrsz, datasz)) return type Memory#(addrsz, datasz) *)
    Definition mkMemory := Build_Memory mkMemoryModule%kami (instancePrefix--"doMem").
    End Section'mkMemory.
End module'mkMemory.

Definition mkMemory := module'mkMemory.mkMemory.
Hint Unfold mkMemory : ModuleDefs.
Hint Unfold module'mkMemory.mkMemory : ModuleDefs.
Hint Unfold module'mkMemory.mkMemoryModule : ModuleDefs.

(* * interface ToHost#(datasz) *)
Record ToHost := {
    ToHost'modules: Modules;
    ToHost'toHost : string;
}.

Hint Unfold ToHost'modules : ModuleDefs.
Hint Unfold ToHost'toHost : ModuleDefs.

Definition ProcInitFields (addrsz : nat) (pgmsz : nat) (instsz : nat) (rfsz : nat) (datasz : nat) := (STRUCT {
    "pcInit" :: Bit pgmsz
}).
Definition ProcInit  (addrsz : nat) (pgmsz : nat) (instsz : nat) (rfsz : nat) (datasz : nat) := Struct (ProcInitFields addrsz pgmsz instsz rfsz datasz).

Module module'procSpec.
    Section Section'procSpec.
    Variable addrsz : nat.
    Variable datasz : nat.
    Variable instsz : nat.
    Variable rfsz : nat.
    Variable pgmsz : nat.
    Variable instancePrefix: string.
    Variable procInit: ConstT (ProcInit addrsz pgmsz instsz rfsz datasz).
    Variable dec : Decoder.
    Variable exec : Executer. 
    Variable tohost: ToHost.
        (* method bindings *)
    Let initval : ConstT (Bit pgmsz) := $0.
    Let pc := mkReg (Bit pgmsz) (instancePrefix--"pc") (initval)%bk.
    Let rf := mkRegFileFull (Bit datasz) (Bit datasz) (instancePrefix--"rf").
    Let mem := mkMemory (addrsz) (datasz) (instancePrefix--"mem").
    Let pgm := mkRegFileFull (Bit pgmsz) (Bit datasz) (instancePrefix--"pgm").
    Let pc_read : string := (Reg'_read pc).
    Let pc_write : string := (Reg'_write pc).
    (* instance methods *)
    Let decgetAddr : string := (Decoder'getAddr dec).
    Let decgetDst : string := (Decoder'getDst dec).
    Let decgetOp : string := (Decoder'getOp dec).
    Let decgetSrc1 : string := (Decoder'getSrc1 dec).
    Let decgetSrc2 : string := (Decoder'getSrc2 dec).
    Let execexecArith : string := (Executer'execArith exec).
    Let memdoMem : string := (Memory'doMem mem).
    Let pgmsub : string := (RegFile'sub pgm).
    Let rfsub : string := (RegFile'sub rf).
    Let rfupd : string := (RegFile'upd rf).
    Let tohosttoHost : string := (ToHost'toHost tohost).
    Definition procSpecModule: Modules := (BKMODULE {
        (BKMod (Reg'modules pc :: nil))
    with (BKMod (RegFile'modules rf :: nil))
    with (BKMod (Memory'modules mem :: nil))
    with (BKMod (RegFile'modules pgm :: nil))
    with (BKMod (Decoder'modules dec :: nil))
    with (BKMod (Executer'modules exec :: nil))
    with Rule instancePrefix--"doArith" :=
    (
        CallM pc_v : Bit pgmsz (* regRead *) <- pc_read();
        CallM inst : Bit instsz <- pgmsub( #pc_v : Bit pgmsz );
        CallM op : Bit 2 <- decgetOp( #inst : Bit instsz );
        Assert((#op == $$opArith));
       CallM inst : Bit instsz (* varbinding *) <-  pgmsub (#pc_v : Bit pgmsz);
       CallM op : Bit 2 (* varbinding *) <-  decgetOp (#inst : Bit instsz);
       CallM src1 : Bit datasz (* varbinding *) <-  decgetSrc1 (#inst : Bit instsz);
       CallM src2 : Bit datasz (* varbinding *) <-  decgetSrc2 (#inst : Bit instsz);
       CallM dst : Bit datasz (* varbinding *) <-  decgetDst (#inst : Bit instsz);
       CallM val1 : Bit instsz (* varbinding *) <-  rfsub (#src1 : Bit datasz);
       CallM val2 : Bit instsz (* varbinding *) <-  rfsub (#src2 : Bit datasz);
       CallM dval : Bit instsz (* varbinding *) <-  execexecArith (#op : OpArithK) (#val1 : Bit instsz) (#val2 : Bit instsz);
               CallM unused : Void (* actionBinding *) <- rfupd (#dst : Bit datasz) (#dval : Bit instsz);
               CallM pc_write ( (#pc_v + $1) : Bit pgmsz );
        Retv ) (* rule doArith *)
    with Rule instancePrefix--"doLoad" :=
      (
        CallM pc_v : Bit pgmsz (* regRead *) <- pc_read();
          CallM inst : Bit instsz <- pgmsub( #pc_v : Bit pgmsz );
          CallM op : Bit 2 <- decgetOp( #inst : Bit instsz );

          Assert((#op == $$opLd));
          CallM addr : Bit datasz (* varbinding *) <-  decgetAddr (#inst : Bit instsz);
          CallM dst : Bit datasz (* varbinding *) <-  decgetDst (#inst : Bit instsz);
          CallM val : Bit instsz (* actionBinding *) <- memdoMem (STRUCT { "addr" ::= (#addr); "data" ::= $0; "isLoad" ::= ($$(natToWord 1 1))  }%kami_expr : MemRq datasz instsz);
          CallM call0 : Void <-  rfupd (#dst : Bit datasz) (#val : Bit instsz);
          CallM pc_write ( (#pc_v + $1) : Bit pgmsz );
          Retv ) (* rule doLoad *)
    with Rule instancePrefix--"doStore" :=
    (
        CallM pc_v : Bit pgmsz (* regRead *) <- pc_read();
        CallM inst : Bit instsz <- pgmsub( #pc_v : Bit pgmsz );
        CallM op : Bit 2 <- decgetOp( #inst : Bit instsz );

        Assert((#op == $$opSt));
       CallM addr : Bit datasz (* varbinding *) <-  decgetAddr (#inst : Bit instsz);
       CallM src : Bit datasz (* varbinding *) <-  decgetSrc1 (#inst : Bit instsz);
       CallM val : Bit instsz (* varbinding *) <-  rfsub (#src : Bit datasz);
               CallM unused : Bit instsz (* actionBinding *) <- memdoMem (STRUCT { "addr" ::= (#addr); "data" ::= (#val); "isLoad" ::= ($$(natToWord 1 0))  }%kami_expr : MemRq datasz instsz);
               CallM pc_write ( (#pc_v + $1) : Bit pgmsz );
        Retv ) (* rule doStore *)
    with Rule instancePrefix--"doHost" :=
    (
        CallM pc_v : Bit pgmsz (* regRead *) <- pc_read();
        CallM inst : Bit instsz <- pgmsub( #pc_v : Bit pgmsz );
        CallM op : Bit 2 <- decgetOp( #inst : Bit instsz );

        Assert((#op == $$opTh));
       CallM src1 : Bit datasz (* varbinding *) <-  decgetSrc1 (#inst : Bit instsz);
       CallM val1 : Bit instsz (* varbinding *) <-  rfsub (#src1 : Bit datasz);
               CallM unused : Void (* actionBinding *) <- tohosttoHost (#val1 : Bit instsz);
               CallM pc_write ( (#pc_v + $1) : Bit pgmsz );
        Retv ) (* rule doHost *)
    }). (* procSpec *)

(* Module procSpec type ProcInit#(datasz, datasz, instsz, datasz, instsz) -> ToHost#(instsz) -> Module#(Empty) return type ToHost#(instsz) *)
    Definition procSpec := Build_Empty procSpecModule%kami.
    End Section'procSpec.
End module'procSpec.

Definition procSpec := module'procSpec.procSpec.
Hint Unfold procSpec : ModuleDefs.
Hint Unfold module'procSpec.procSpec : ModuleDefs.

