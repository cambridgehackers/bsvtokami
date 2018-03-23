Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Definition \$methodready (m: (word 1)): (word 0) := 
        Ret $1
.

Definition \$finish: (word 0) := 
        Ret $1
.

Section GCD.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Definition mkGCDModule := MODULE {

    Register ^"n" : Bit 32 <- $0
    with Register ^"m" : Bit 32 <- $0
    with Rule ^"swap" :=
        Read m_v : Bit 32 <- ^"m";
        Read n_v : Bit 32 <- ^"n";
        Assert((&& (> #n_v #m_v) (!= #m_v $0)));
        Write ^"n" : Bit 32 <- #m_v;
        Write ^"m" : Bit 32 <- #n_v;
        Retv (* rule swap *)

    with Rule ^"sub" :=
        Read m_v : Bit 32 <- ^"m";
        Read n_v : Bit 32 <- ^"n";
        Assert((&& (<= #n_v #m_v) (!= #m_v $0)));
        Write ^"m" : Bit 32 <- (- #m_v #n_v);
        Retv (* rule sub *)

    with Method ^"set_n" (in_n: (word 32)) : Void := 
        Write ^"n" : Bit 32 <- #in_n;
        Retv

    with Method ^"set_m" (in_m: (word 32)) : Void := 
        Write ^"m" : Bit 32 <- #in_m;
        Retv

    with Method ^"result" () : (word 32) := 
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

            Call gcd <- mkGCD(); (* method call 1 *)
    with Register ^"started" : Bit 1 <- $0
    with Register ^"dv" : Bit 32 <- $0
    with Rule ^"rl_start" :=
        Read started_v : Bit 1 <- ^"started";
        Assert((&& (&& (== #started_v $0)         Call $methodready(#gcd); (* method call expr *)
)         Call $methodready(#gcd); (* method call expr *)
));
        Call gcdset_n($100); (* method call expr *)
        Call gcdset_m($20); (* method call expr *)
        Write ^"started" : Bit 1 <- $1;
        Retv (* rule rl_start *)

    with Rule ^"rl_display" :=
        Assert(        Call $methodready(#gcd); (* method call expr *)
);
        Write ^"dv" : Bit 32 <-         Call gcdresult(); (* method call expr *)
;
        Call $finish(); (* method call expr *)
        Retv (* rule rl_display *)

    }. (*mkMain *)

    Definition mkMain := (mkMainModule)%kami.
End Main.
