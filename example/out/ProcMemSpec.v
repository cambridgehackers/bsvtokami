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

Notation NumRegs := 32 (only parsing).
Notation RegFileSz := (Nat.log2_up 32) (only parsing).

Definition NumInstrs := 8.
Definition PgmSz := Nat.log2_up NumInstrs.

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
        BKCall ldval : Bit DataSz (* varbinding *) <-  (* translateCall *) mem'sub ((#addr) : Bit AddrSz) ;
                Ret #ldval
        ) else (
        
        LET addr : Bit AddrSz (* non-call varbinding *) <- (#req @% "addr") ;
                LET newval : Bit DataSz (* non-call varbinding *) <- (#req @% "data") ;
                BKCall unused : Void (* actionBinding *) <- mem'upd ((#addr) : Bit AddrSz) ((#newval) : Bit DataSz) ;
        BKCall placeholder : Bit DataSz (* varbinding *) <-  (* translateCall *) mem'sub ((#addr) : Bit AddrSz) ;
                Ret #placeholder) as retval
 ;
        Ret #retval    )

    }). (* mkMemory *)

    Close Scope kami_expr.

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
    Let (* action binding *) mem := mkMemory (instancePrefix--"mem").
    (* instance methods *)
    Let dec'getAddr : string := (Decoder'getAddr dec).
    Let dec'getDst : string := (Decoder'getDst dec).
    Let dec'getOp : string := (Decoder'getOp dec).
    Let dec'getSrc1 : string := (Decoder'getSrc1 dec).
    Let dec'getSrc2 : string := (Decoder'getSrc2 dec).
    Let dec'isOp : string := (Decoder'isOp dec).
    Let exec'execArith : string := (Executer'execArith exec).
    Let mem'doMem : string := (Memory'doMem mem).
    Let pgm'sub : string := (RegFile'sub pgm).
    Let rf'sub : string := (RegFile'sub rf).
    Let rf'upd : string := (RegFile'upd rf).
    Let tohost'toHost : string := (ToHost'toHost tohost).
    Local Open Scope kami_expr.

    Definition procSpecModule: Mod :=
         (BKMODULE {
        Register pc : Bit PgmSz <-  (* intwidth *) (natToWord PgmSz 0)
    with (BKMod (RegFile'mod rf :: nil))
    with (BKMod (Memory'mod mem :: nil))
    with Rule instancePrefix--"doArith" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call1 : Bit InstrSz <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call0 : Bool <-  (* translateCall *) dec'isOp ((#call1) : Bit InstrSz) (($$ (* isConstT *)opArith) : OpK) ;

        Assert(#call0) ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall op : OpK (* varbinding *) <-  (* translateCall *) dec'getOp ((#inst) : Bit InstrSz) ;
       BKCall src1 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getSrc1 ((#inst) : Bit InstrSz) ;
       BKCall src2 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getSrc2 ((#inst) : Bit InstrSz) ;
       BKCall dst : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getDst ((#inst) : Bit InstrSz) ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#src1) : Bit RegFileSz) ;
       BKCall val2 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#src2) : Bit RegFileSz) ;
       BKCall dval : Bit DataSz (* varbinding *) <-  (* translateCall *) exec'execArith ((#op) : OpArithK) ((#val1) : Bit DataSz) ((#val2) : Bit DataSz) ;
               BKCall unused : Void (* actionBinding *) <- rf'upd ((#dst) : Bit RegFileSz) ((#dval) : Bit DataSz) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule doArith *)
    with Rule instancePrefix--"doLoad" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call3 : Bit InstrSz <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call2 : Bool <-  (* translateCall *) dec'isOp ((#call3) : Bit InstrSz) (($$ (* isConstT *)opLd) : OpK) ;

        Assert(#call2) ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall addr : Bit AddrSz (* varbinding *) <-  (* translateCall *) dec'getAddr ((#inst) : Bit InstrSz) ;
       BKCall dst : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getDst ((#inst) : Bit InstrSz) ;
               BKCall val : Bit DataSz (* actionBinding *) <- mem'doMem ((STRUCT { "addr" ::= (#addr) ; "data" ::= ($$ (* intwidth *) (natToWord 32 0)) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 1))  }%kami_expr) : MemRq) ;
       BKCall call4 : Void <-  (* translateCall *) rf'upd ((#dst) : Bit RegFileSz) ((#val) : Bit DataSz) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule doLoad *)
    with Rule instancePrefix--"doStore" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call6 : Bit InstrSz <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call5 : Bool <-  (* translateCall *) dec'isOp ((#call6) : Bit InstrSz) (($$ (* isConstT *)opSt) : OpK) ;

        Assert(#call5) ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall addr : Bit AddrSz (* varbinding *) <-  (* translateCall *) dec'getAddr ((#inst) : Bit InstrSz) ;
       BKCall src : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getSrc1 ((#inst) : Bit InstrSz) ;
       BKCall val : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#src) : Bit RegFileSz) ;
               BKCall unused : Bit DataSz (* actionBinding *) <- mem'doMem ((STRUCT { "addr" ::= (#addr) ; "data" ::= (#val) ; "isLoad" ::= ($$ (* intwidth *) (natToWord 1 0))  }%kami_expr) : MemRq) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule doStore *)
    with Rule instancePrefix--"doHost" :=
    (
        Read pc_v : Bit PgmSz <- pc ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call8 : Bit InstrSz <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall call7 : Bool <-  (* translateCall *) dec'isOp ((#call8) : Bit InstrSz) (($$ (* isConstT *)opTh) : OpK) ;

        Assert(#call7) ;
       BKCall inst : Bit InstrSz (* varbinding *) <-  (* translateCall *) pgm'sub ((#pc_v) : Bit PgmSz) ;
       BKCall src1 : Bit RegFileSz (* varbinding *) <-  (* translateCall *) dec'getSrc1 ((#inst) : Bit InstrSz) ;
       BKCall val1 : Bit DataSz (* varbinding *) <-  (* translateCall *) rf'sub ((#src1) : Bit RegFileSz) ;
               BKCall unused : Void (* actionBinding *) <- tohost'toHost ((#val1) : Bit DataSz) ;
               Write pc : Bit PgmSz <- (#pc_v + $$ (* intwidth *) (natToWord PgmSz 1)) ;
        Retv ) (* rule doHost *)
    }). (* procSpec *)

    Close Scope kami_expr.

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

