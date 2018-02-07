Require Import Bool String List.
Require Import Lib.CommonTactics Lib.ilist Lib.Word.
Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.

Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Wf.
Require Import Kami.Inline Kami.InlineFacts.
Require Import Kami.RefinementFacts Kami.Decomposition.
Require Import Kami.Tactics.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section GCD.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Definition mkGCDModule := MODULE {

    Register ^"n" : Bit 32 <- $0
    with Register ^"m" : Bit 32 <- $0
    with Rule ^"swap" :=
        Read m_v : Bit 32 <- ^"m";
        Read n_v : Bit 32 <- ^"n";
        Assert(((#n_v > #m_v) && (#m_v != $0)));
        Write ^"n" : Bit 32 <- #m_v;
        Write ^"m" : Bit 32 <- #n_v;
        Retv (* rule swap *)

    with Rule ^"sub" :=
        Read m_v : Bit 32 <- ^"m";
        Read n_v : Bit 32 <- ^"n";
        Assert(((#n_v <= #m_v) && (#m_v != $0)));
        Write ^"m" : Bit 32 <- (#m_v - #n_v);
        Retv (* rule sub *)

    with Method ^"set_n" (in_n: Bit 32) : Void := 
        Write ^"n" : Bit 32 <- #in_n;
        Retv

    with Method ^"set_m" (in_m: Bit 32) : Void := 
        Write ^"m" : Bit 32 <- #in_m;
        Retv

    with Method ^"result" () : Bit 32 := 
        Read n_v : Bit 32 <- "n";
        Ret #n_v

    }. (*mkGCD *)

    Definition mkGCD := (mkGCDModule)%kami.
End GCD.
Section Main.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Definition gcdresult := MethodSig (^"gcd"--"result") () : Void.
    Definition gcdset_m := MethodSig (^"gcd"--"set_m") () : Void.
    Definition gcdset_n := MethodSig (^"gcd"--"set_n") () : Void.
    Definition mkMainModule := MODULE {

            (* instantiate gcd *)
    Register ^"started" : Bit 1 <- $0
    with Rule ^"rl_init" :=
        Retv (* rule rl_init *)

    with Rule ^"rl_start" :=
        Read started_v : Bit 1 <- ^"started";
        Assert((#started_v == $0));
        Call gcdset_n($100); (* method call expr *)
        Call gcdset_m($20); (* method call expr *)
        Write ^"started" : Bit 1 <- $1;
        Retv (* rule rl_start *)

    with Rule ^"rl_display" :=
        Call v <- gcdresult(); (* method call 1 *)
        Retv (* rule rl_display *)

    }. (*mkMain *)

    Definition mkMainInstances := (mkGCD("gcd"))%kami.
    Definition mkMain := (mkMainInstances ++ mkMainModule)%kami.
End Main.
