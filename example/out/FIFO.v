Require Import Bool String List Arith.
Require Import Omega.
Require Import micromega.Lia.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface FIFO#(element_type) *)
Record FIFO := {
    FIFO'modules: Modules;
    FIFO'first : string;
    FIFO'enq : string;
    FIFO'deq : string;
    FIFO'clear : string;
}.

Hint Unfold FIFO'modules : ModuleDefs.
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
    (* method binding *) Let v := mkRegU (element_type) (instancePrefix--"v").
    (* method binding *) Let valid := mkReg (Bit 1) (instancePrefix--"valid") (initialValid)%bk.
    (* method binding *) Let v_read : string := (Reg'_read v).
    (* method binding *) Let v_write : string := (Reg'_write v).
    (* method binding *) Let valid_write : string := (Reg'_write valid).
    Definition mkFIFOModule: Modules := (BKMODULE {
        (BKMod (Reg'modules v :: nil))
    with (BKMod (Reg'modules valid :: nil))
    with Method instancePrefix--"first" () : element_type :=
    (
CallM v_v : element_type (* methoddef regread *) <- v_read();
        LET result : element_type <- #v_v;
        Ret #result    )

    with Method instancePrefix--"enq" (new_v : element_type) : Void :=
    (
        CallM v_write ( #new_v : element_type );
        CallM valid_write ( $$(natToWord 1 1) : Bit 1 );
        Retv    )

    with Method instancePrefix--"deq" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    with Method instancePrefix--"clear" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    }). (* mkFIFO *)

(* Module mkFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO := Build_FIFO mkFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkFIFO.
End module'mkFIFO.

Definition mkFIFO := module'mkFIFO.mkFIFO.
Hint Unfold mkFIFO : ModuleDefs.
Hint Unfold module'mkFIFO.mkFIFO : ModuleDefs.
Hint Unfold module'mkFIFO.mkFIFOModule : ModuleDefs.

Module module'mkLFIFO.
    Section Section'mkLFIFO.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable esz: nat.
    (* let bindings *)
    Let initialValid : ConstT (Bit 1) := ($0)%kami.
        (* method bindings *)
    (* method binding *) Let v := mkRegU (element_type) (instancePrefix--"v").
    (* method binding *) Let valid := mkReg (Bit 1) (instancePrefix--"valid") (initialValid)%bk.
    (* method binding *) Let v_read : string := (Reg'_read v).
    (* method binding *) Let v_write : string := (Reg'_write v).
    (* method binding *) Let valid_write : string := (Reg'_write valid).
    Definition mkLFIFOModule: Modules.
        refine  (BKMODULE {
        (BKMod (Reg'modules v :: nil))
    with (BKMod (Reg'modules valid :: nil))
    with Method instancePrefix--"first" () : element_type :=
    (
CallM v_v : element_type (* methoddef regread *) <- v_read();
        LET result : element_type <- #v_v;
        Ret #result    )

    with Method instancePrefix--"enq" (new_v : element_type) : Void :=
    (
        CallM v_write ( #new_v : element_type );
        CallM valid_write ( $$(natToWord 1 1) : Bit 1 );
        Retv    )

    with Method instancePrefix--"deq" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    with Method instancePrefix--"clear" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    }); abstract omega. Qed. (* mkLFIFO *)

(* Module mkLFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkLFIFO := Build_FIFO mkLFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkLFIFO.
End module'mkLFIFO.

Definition mkLFIFO := module'mkLFIFO.mkLFIFO.
Hint Unfold mkLFIFO : ModuleDefs.
Hint Unfold module'mkLFIFO.mkLFIFO : ModuleDefs.

Module module'mkFIFO1.
    Section Section'mkFIFO1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    (* let bindings *)
    Let initialValid : ConstT (Bit 1) := ($0)%kami.
        (* method bindings *)
    (* method binding *) Let v := mkRegU (element_type) (instancePrefix--"v").
    (* method binding *) Let valid := mkReg (Bit 1) (instancePrefix--"valid") (initialValid)%bk.
    (* method binding *) Let v_read : string := (Reg'_read v).
    (* method binding *) Let v_write : string := (Reg'_write v).
    (* method binding *) Let valid_write : string := (Reg'_write valid).
    Definition mkFIFO1Module: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules v :: nil))
    with (BKMod (Reg'modules valid :: nil))
    with Method instancePrefix--"first" () : element_type :=
    (
CallM v_v : element_type (* methoddef regread *) <- v_read();
        Ret #v_v    )

    with Method instancePrefix--"enq" (new_v : element_type) : Void :=
    (
        CallM v_write ( #new_v : element_type );
        CallM valid_write ( $$(natToWord 1 1) : Bit 1 );
        Retv    )

    with Method instancePrefix--"deq" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    with Method instancePrefix--"clear" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    }). (* mkFIFO1 *)

(* Module mkFIFO1 type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO1 := Build_FIFO mkFIFO1Module%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkFIFO1.
End module'mkFIFO1.

Definition mkFIFO1 := module'mkFIFO1.mkFIFO1.
Hint Unfold mkFIFO1 : ModuleDefs.
Hint Unfold module'mkFIFO1.mkFIFO1 : ModuleDefs.
Hint Unfold module'mkFIFO1.mkFIFO1Module : ModuleDefs.

Module module'mkSizedFIFO.
    Section Section'mkSizedFIFO.
    Variable element_type : Kind.
    Variable instancePrefix: string.
    Variable n: Integer.
    (* let bindings *)
    Let initialValid : ConstT (Bit 1) := ($0)%kami.
        (* method bindings *)
    (* method binding *) Let v := mkRegU (element_type) (instancePrefix--"v").
    (* method binding *) Let valid := mkReg (Bit 1) (instancePrefix--"valid") (initialValid)%bk.
    (* method binding *) Let v_read : string := (Reg'_read v).
    (* method binding *) Let v_write : string := (Reg'_write v).
    (* method binding *) Let valid_write : string := (Reg'_write valid).
    Definition mkSizedFIFOModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules v :: nil))
    with (BKMod (Reg'modules valid :: nil))
    with Method instancePrefix--"first" () : element_type :=
    (
CallM v_v : element_type (* methoddef regread *) <- v_read();
        Ret #v_v    )

    with Method instancePrefix--"enq" (new_v : element_type) : Void :=
    (
        CallM v_write ( #new_v : element_type );
        CallM valid_write ( $$(natToWord 1 1) : Bit 1 );
        Retv    )

    with Method instancePrefix--"deq" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    with Method instancePrefix--"clear" () : Void :=
    (
        CallM valid_write ( $$(natToWord 1 0) : Bit 1 );
        Retv    )

    }). (* mkSizedFIFO *)

(* Module mkSizedFIFO type Integer -> Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkSizedFIFO := Build_FIFO mkSizedFIFOModule%kami (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    End Section'mkSizedFIFO.
End module'mkSizedFIFO.

Definition mkSizedFIFO := module'mkSizedFIFO.mkSizedFIFO.
Hint Unfold mkSizedFIFO : ModuleDefs.
Hint Unfold module'mkSizedFIFO.mkSizedFIFO : ModuleDefs.
Hint Unfold module'mkSizedFIFO.mkSizedFIFOModule : ModuleDefs.

