Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface FIFO#(element_type) *)
Record FIFO := {
    FIFO'mod: Mod;
    FIFO'first : string;
    FIFO'enq : string;
    FIFO'deq : string;
    FIFO'clear : string;
}.

Hint Unfold FIFO'mod : ModuleDefs.
Hint Unfold FIFO'first : ModuleDefs.
Hint Unfold FIFO'enq : ModuleDefs.
Hint Unfold FIFO'deq : ModuleDefs.
Hint Unfold FIFO'clear : ModuleDefs.

Module module'mkFIFO.
    Section Section'mkFIFO.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable esz: nat.
    (* let bindings *)
    Let initialValid : ConstT (Bit 1) := ($0)%kami.
        (* method bindings *)
    Let v := mkRegU (element_type) (instancePrefix--"v").
    Let valid := mkReg (instancePrefix--"valid") (initialValid)%bk.
    Let v_read : string := (Reg'_read v).
    Let v_write : string := (Reg'_write v).
    Let valid_write : string := (Reg'_write valid).
    Local Open Scope kami_expr.

    Definition mkFIFOModule: Mod := (BKMODULE {
        (BKMod (Reg'mod v :: nil))
    with (BKMod (Reg'mod valid :: nil))
    with Method (instancePrefix--"first") () : element_type :=
    (
Call v_v : element_type (* methoddef regread *) <- v_read();
        LET result : element_type <- #v_v ;
        Ret #result    )

    with Method (instancePrefix--"enq") (new_v : element_type) : Void :=
    (
        Call v_write ( (#new_v) : element_type ) ;
        Call valid_write ( ($1) : Bit 1 ) ;
        Retv    )

    with Method (instancePrefix--"deq") () : Void :=
    (
        Call valid_write ( ($0) : Bit 1 ) ;
        Retv    )

    with Method (instancePrefix--"clear") () : Void :=
    (
        Call valid_write ( ($0) : Bit 1 ) ;
        Retv    )

    }). (* mkFIFO *)

(* Module mkFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO := Build_FIFO mkFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkFIFO.
End module'mkFIFO.

Definition mkFIFO := module'mkFIFO.mkFIFO.
Hint Unfold mkFIFO : ModuleDefs.
Hint Unfold module'mkFIFO.mkFIFO : ModuleDefs.

Module module'mkLFIFO.
    Section Section'mkLFIFO.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable esz: nat.
    (* let bindings *)
    Let initialValid : ConstT (Bit 1) := ($0)%kami.
        (* method bindings *)
    Let v := mkRegU (element_type) (instancePrefix--"v").
    Let valid := mkReg (instancePrefix--"valid") (initialValid)%bk.
    Let v_read : string := (Reg'_read v).
    Let v_write : string := (Reg'_write v).
    Let valid_write : string := (Reg'_write valid).
    Local Open Scope kami_expr.

    Definition mkLFIFOModule: Mod := (BKMODULE {
        (BKMod (Reg'mod v :: nil))
    with (BKMod (Reg'mod valid :: nil))
    with Method (instancePrefix--"first") () : element_type :=
    (
Call v_v : element_type (* methoddef regread *) <- v_read();
        LET result : element_type <- #v_v ;
        Ret #result    )

    with Method (instancePrefix--"enq") (new_v : element_type) : Void :=
    (
        Call v_write ( (#new_v) : element_type ) ;
        Call valid_write ( ($1) : Bit 1 ) ;
        Retv    )

    with Method (instancePrefix--"deq") () : Void :=
    (
        Call valid_write ( ($0) : Bit 1 ) ;
        Retv    )

    with Method (instancePrefix--"clear") () : Void :=
    (
        Call valid_write ( ($0) : Bit 1 ) ;
        Retv    )

    }). (* mkLFIFO *)

(* Module mkLFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkLFIFO := Build_FIFO mkLFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkLFIFO.
End module'mkLFIFO.

Definition mkLFIFO := module'mkLFIFO.mkLFIFO.
Hint Unfold mkLFIFO : ModuleDefs.
Hint Unfold module'mkLFIFO.mkLFIFO : ModuleDefs.

