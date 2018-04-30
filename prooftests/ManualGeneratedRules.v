Require Import Bool String List Arith Nat.
Require Import Kami.
Require Import Kami.Lib.NatLib.
Require Import Lib.Indexer.
Require Import Bsvtokami.
Require Import ZArith.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Fixpoint toBinaryP (p: positive) : string :=
  match p with
  | xI p' => String "1" (toBinaryP p')
  | xO p' => String "0" (toBinaryP p')
  | xH => ""
  end.

Definition toBinaryN (n: N): string :=
  match n with
  | N0 => "0"
  | Npos p => toBinaryP p
  end.

Definition toBinary (n: nat) := (toBinaryN (N.of_nat n)).

Fixpoint appendInModule (im1: InModule) (im2: InModule) : InModule :=
    match im1 with
    | NilInModule => im2
    | ConsInModule e im1' => ConsInModule e (appendInModule im1' im2)
end.

Definition moduleStatement stmt: InModule :=
    (ConsInModule stmt NilInModule).

Notation "'MODULESTMTS' { s1 'with' .. 'with' sN }" :=
  (makeModule (appendInModule s1 .. (appendInModule sN NilInModule) ..))
    (at level 0, only parsing).

Notation "'STMTS' { s1 'with' .. 'with' sN }" :=
  (appendInModule s1 .. (appendInModule sN NilInModule) ..)
    (at level 0, only parsing).

Notation "'STMTSR' { s1 'with' .. 'with' sN } SL" :=
  (ConsInModule s1 .. (ConsInModule sN SL) ..)
    (at level 0, only parsing).

Section Consumer.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable extName: string.
    Definition extextCall := MethodSig (extName--"extCall") (Bit 32) : Void.
    Definition mkConsumerModule := MODULE {

    Method ^"send" (v: (Bit 32)) : Void := 
        Call extextCall(#v); (* method call expr *)
        Retv

    }. (*mkConsumer *)

    Definition mkConsumer := (mkConsumerModule)%kami.
End Consumer.

Section Producer.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable consumerName: string.
    Variable numRegs : nat.
    Definition consumersend := MethodSig (consumerName--"send") (Bit 32) : Void.
    Let loopM :=
       fix loopM' (n: nat) : InModule :=
       match n with
       | 0 => NilInModule
       | S n' => STMTSR {
       	      	    (Register ^"data"--(toBinary n) : Bit 32 <- $0)%kami
		    with
		    (Rule moduleName--"produce"--(toBinary n) :=
			Read data_v : Bit 32 <- ^"data"--(toBinary n);
			Call consumersend(#data_v); (* method call expr *)
			Write ^"data"--(toBinary n) : Bit 32 <- (#data_v + $1);
			Retv (* rule produce *))%kami
		    }
       	            (loopM' n')
       end.
    Definition mkProducerModule := MODULESTMTS {
         (loopM numRegs)

    }. (*mkProducer *)

    Definition mkProducer := (mkProducerModule)%kami.
End Producer.
Section ProduceConsume.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable extpcName: string.
    Variable numRegs : nat.

    Definition extpcextCall := MethodSig (extpcName--"extCall") (Bit 32) : Void.

    Let loopM :=
       fix loopM' (limit: nat) (m: nat) : InModule :=
       match m with
       | S m' =>  let n := (numRegs - m) in
       	          STMTSR {
       	          (Register ^"pcdata"--(toBinary n) : Bit 32 <- $0)%kami
		  with
    		  (Rule ^"produce_consume"--(toBinary n) :=
			Read data_v : Bit 32 <- ^"pcdata"--(toBinary n);
			Call extpcextCall(#data_v); (* method call expr *)
			Write ^"pcdata"--(toBinary n) : Bit 32 <- (#data_v + $1);
			Write ^"pcdata"--(toBinary n) : Bit 32 <- (#data_v + $2);
			Retv)%kami }
	          (loopM' limit m')
       | 0 => NilInModule
       end.

    Definition mkProduceConsumeModule := MODULESTMTS {

        (loopM numRegs numRegs)
 (* rule produce_consume *)

    }. (*mkProduceConsume *)

    Definition mkProduceConsume := (mkProduceConsumeModule)%kami.
End ProduceConsume.
