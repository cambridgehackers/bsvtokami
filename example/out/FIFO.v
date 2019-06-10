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
        (* method bindings *)
    Let v : string := instancePrefix--"v".
    Let valid : string := instancePrefix--"valid".
    Local Open Scope kami_expr.

    Definition mkFIFOModule: Mod :=
         (BKMODULE {
        Register v : element_type <- Default
    with Register valid : Bit 1 <-  (* intwidth *) (natToWord 1 0)
    with Method (instancePrefix--"first") () : element_type :=
    (
        Read v_v : element_type <- "v" ;        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        LET result : element_type (* non-call varbinding *) <- #v_v ;
        Ret #result    )

    with Method (instancePrefix--"enq") (new_v : element_type) : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 0))) ;
        Write v : element_type <- #new_v  ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 1)  ;
        Retv    )

    with Method (instancePrefix--"deq") () : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    with Method (instancePrefix--"clear") () : Void :=
    (
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    }). (* mkFIFO *)

    Hint Unfold mkFIFOModule : ModuleDefs.
(* Module mkFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO := Build_FIFO mkFIFOModule (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    Hint Unfold mkFIFO : ModuleDefs.
    Hint Unfold mkFIFOModule : ModuleDefs.

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
        (* method bindings *)
    Let v : string := instancePrefix--"v".
    Let valid : string := instancePrefix--"valid".
    Local Open Scope kami_expr.

    Definition mkLFIFOModule: Mod :=
         (BKMODULE {
        Register v : element_type <- Default
    with Register valid : Bit 1 <-  (* intwidth *) (natToWord 1 0)
    with Method (instancePrefix--"first") () : element_type :=
    (
        Read v_v : element_type <- "v" ;        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        LET result : element_type (* non-call varbinding *) <- #v_v ;
        Ret #result    )

    with Method (instancePrefix--"enq") (new_v : element_type) : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 0))) ;
        Write v : element_type <- #new_v  ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 1)  ;
        Retv    )

    with Method (instancePrefix--"deq") () : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    with Method (instancePrefix--"clear") () : Void :=
    (
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    }). (* mkLFIFO *)

    Hint Unfold mkLFIFOModule : ModuleDefs.
(* Module mkLFIFO type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkLFIFO := Build_FIFO mkLFIFOModule (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    Hint Unfold mkLFIFO : ModuleDefs.
    Hint Unfold mkLFIFOModule : ModuleDefs.

    End Section'mkLFIFO.
End module'mkLFIFO.

Definition mkLFIFO := module'mkLFIFO.mkLFIFO.
Hint Unfold mkLFIFO : ModuleDefs.
Hint Unfold module'mkLFIFO.mkLFIFO : ModuleDefs.
Hint Unfold module'mkLFIFO.mkLFIFOModule : ModuleDefs.

Module module'mkFIFO1.
    Section Section'mkFIFO1.
    Variable element_type : Kind.
    Variable instancePrefix: string.
        (* method bindings *)
    Let v : string := instancePrefix--"v".
    Let valid : string := instancePrefix--"valid".
    Local Open Scope kami_expr.

    Definition mkFIFO1Module: Mod :=
         (BKMODULE {
        Register v : element_type <- Default
    with Register valid : Bit 1 <-  (* intwidth *) (natToWord 1 0)
    with Method (instancePrefix--"first") () : element_type :=
    (
        Read v_v : element_type <- "v" ;        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        Ret #v_v    )

    with Method (instancePrefix--"enq") (new_v : element_type) : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 0))) ;
        Write v : element_type <- #new_v  ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 1)  ;
        Retv    )

    with Method (instancePrefix--"deq") () : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    with Method (instancePrefix--"clear") () : Void :=
    (
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    }). (* mkFIFO1 *)

    Hint Unfold mkFIFO1Module : ModuleDefs.
(* Module mkFIFO1 type Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkFIFO1 := Build_FIFO mkFIFO1Module (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    Hint Unfold mkFIFO1 : ModuleDefs.
    Hint Unfold mkFIFO1Module : ModuleDefs.

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
        (* method bindings *)
    Let v : string := instancePrefix--"v".
    Let valid : string := instancePrefix--"valid".
    Local Open Scope kami_expr.

    Definition mkSizedFIFOModule: Mod :=
         (BKMODULE {
        Register v : element_type <- Default
    with Register valid : Bit 1 <-  (* intwidth *) (natToWord 1 0)
    with Method (instancePrefix--"first") () : element_type :=
    (
        Read v_v : element_type <- "v" ;        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        Ret #v_v    )

    with Method (instancePrefix--"enq") (new_v : element_type) : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 0))) ;
        Write v : element_type <- #new_v  ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 1)  ;
        Retv    )

    with Method (instancePrefix--"deq") () : Void :=
    (
        Read valid_v : Bit 1 <- "valid" ;
        Assert((#valid_v == $$ (* intwidth *) (natToWord 1 1))) ;
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    with Method (instancePrefix--"clear") () : Void :=
    (
        Write valid : Bit 1 <- $$ (* intwidth *) (natToWord 1 0)  ;
        Retv    )

    }). (* mkSizedFIFO *)

    Hint Unfold mkSizedFIFOModule : ModuleDefs.
(* Module mkSizedFIFO type Integer -> Module#(FIFO#(element_type)) return type FIFO#(element_type) *)
    Definition mkSizedFIFO := Build_FIFO mkSizedFIFOModule (instancePrefix--"clear") (instancePrefix--"deq") (instancePrefix--"enq") (instancePrefix--"first").
    Hint Unfold mkSizedFIFO : ModuleDefs.
    Hint Unfold mkSizedFIFOModule : ModuleDefs.

    End Section'mkSizedFIFO.
End module'mkSizedFIFO.

Definition mkSizedFIFO := module'mkSizedFIFO.mkSizedFIFO.
Hint Unfold mkSizedFIFO : ModuleDefs.
Hint Unfold module'mkSizedFIFO.mkSizedFIFO : ModuleDefs.
Hint Unfold module'mkSizedFIFO.mkSizedFIFOModule : ModuleDefs.

