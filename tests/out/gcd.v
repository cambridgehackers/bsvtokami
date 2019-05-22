Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface GCD#(a) *)
Record GCD := {
    GCD'mod: Mod;
    GCD'set_n : string;
    GCD'set_m : string;
    GCD'result : string;
}.

Hint Unfold GCD'mod : ModuleDefs.
Hint Unfold GCD'set_n : ModuleDefs.
Hint Unfold GCD'set_m : ModuleDefs.
Hint Unfold GCD'result : ModuleDefs.

Module module'mkGCD.
    Section Section'mkGCD.
    Variable instancePrefix: string.
        (* method bindings *)
    Local Open Scope kami_expr.

    Definition mkGCDModule: Mod :=
         (BKMODULE {
        Register (instancePrefix--"n") : Bit 32 <- Default
    with Register (instancePrefix--"m") : Bit 32 <- Default
    with Rule instancePrefix--"swap" :=
    (
        Read m_v : Bit 32 <- (instancePrefix--"m") ;
        Read n_v : Bit 32 <- (instancePrefix--"n") ;

        Assert(((#n_v > #m_v) && (#m_v != $$ (* intwidth *) (natToWord 32 0)))) ;
               Write (instancePrefix--"n") : Bit 32 <- #m_v  ;
               Write (instancePrefix--"m") : Bit 32 <- #n_v  ;
        Retv ) (* rule swap *)
    with Rule instancePrefix--"sub" :=
    (
        Read m_v : Bit 32 <- (instancePrefix--"m") ;
        Read n_v : Bit 32 <- (instancePrefix--"n") ;

        Assert(((#n_v <= #m_v) && (#m_v != $$ (* intwidth *) (natToWord 32 0)))) ;
               Write (instancePrefix--"m") : Bit 32 <- (#m_v - #n_v)  ;
        Retv ) (* rule sub *)
    with Method (instancePrefix--"set_n") (in_n : (Bit 32)) : Void :=
    (
        Read m_v : Bit 32 <- (instancePrefix--"m") ;
        Assert((#m_v == $$ (* intwidth *) (natToWord 32 0))) ;
        Write (instancePrefix--"n") : Bit 32 <- #in_n  ;
        Retv    )

    with Method (instancePrefix--"set_m") (in_m : (Bit 32)) : Void :=
    (
        Read m_v : Bit 32 <- (instancePrefix--"m") ;
        Assert((#m_v == $$ (* intwidth *) (natToWord 32 0))) ;
        Write (instancePrefix--"m") : Bit 32 <- #in_m  ;
        Retv    )

    with Method (instancePrefix--"result") () : Bit 32 :=
    (
        Read m_v : Bit 32 <- (instancePrefix--"m") ;
        Read n_v : Bit 32 <- (instancePrefix--"n") ;
        Assert((#m_v == $$ (* intwidth *) (natToWord 32 0))) ;
        Ret #n_v    )

    }). (* mkGCD *)

    Hint Unfold mkGCDModule : ModuleDefs.
(* Module mkGCD type Module#(GCD#(Bit#(32))) return type GCD#(Bit#(32)) *)
    Definition mkGCD := Build_GCD mkGCDModule (instancePrefix--"result") (instancePrefix--"set_m") (instancePrefix--"set_n").
    Hint Unfold mkGCD : ModuleDefs.
    Hint Unfold mkGCDModule : ModuleDefs.

    End Section'mkGCD.
End module'mkGCD.

Definition mkGCD := module'mkGCD.mkGCD.
Hint Unfold mkGCD : ModuleDefs.
Hint Unfold module'mkGCD.mkGCD : ModuleDefs.
Hint Unfold module'mkGCD.mkGCDModule : ModuleDefs.

Module module'mkMain.
    Section Section'mkMain.
    Variable instancePrefix: string.
        (* method bindings *)
    Let (* action binding *) gcd := mkGCD (instancePrefix--"gcd").
    Let started : string := instancePrefix--"started".
    Let dv : string := instancePrefix--"dv".
    (* instance methods *)
    Let gcd'result : string := (GCD'result gcd).
    Let gcd'set_m : string := (GCD'set_m gcd).
    Let gcd'set_n : string := (GCD'set_n gcd).
    Local Open Scope kami_expr.

    Definition mkMainModule: Mod :=
         (BKMODULE {
        (BKMod (GCD'mod gcd :: nil))
    with Register (instancePrefix--"started") : Bit 1 <- Default
    with Register (instancePrefix--"dv") : Bit 32 <- Default
    with Rule instancePrefix--"rl_start" :=
    (
        Read started_v : Bit 1 <- started ;

        Assert((#started_v == $$ (* intwidth *) (natToWord 1 0))) ;
               BKCall unused1 : Void (* actionBinding *) <- gcd'set_n (($$ (* intwidth *) (natToWord 32 100)) : Bit 32)  ;
               BKCall unused2 : Void (* actionBinding *) <- gcd'set_m (($$ (* intwidth *) (natToWord 32 20)) : Bit 32)  ;
               Write (instancePrefix--"started") : Bit 1 <- $$ (* intwidth *) (natToWord 1 1)  ;
        Retv ) (* rule rl_start *)

    }). (* mkMain *)

    Hint Unfold mkMainModule : ModuleDefs.
(* Module mkMain type Module#(Empty) return type Empty *)
    Definition mkMain := Build_Empty mkMainModule.
    Hint Unfold mkMain : ModuleDefs.
    Hint Unfold mkMainModule : ModuleDefs.

    End Section'mkMain.
End module'mkMain.

Definition mkMain := module'mkMain.mkMain.
Hint Unfold mkMain : ModuleDefs.
Hint Unfold module'mkMain.mkMain : ModuleDefs.
Hint Unfold module'mkMain.mkMainModule : ModuleDefs.
