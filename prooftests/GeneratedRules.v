Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.
Require Import ZArith.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

(*
Fixpoint string_of_uint (d:uint) :=
 match d with
 | Nil => EmptyString
 | D0 d => String "0" (string_of_uint d)
 | D1 d => String "1" (string_of_uint d)
 | D2 d => String "2" (string_of_uint d)
 | D3 d => String "3" (string_of_uint d)
 | D4 d => String "4" (string_of_uint d)
 | D5 d => String "5" (string_of_uint d)
 | D6 d => String "6" (string_of_uint d)
 | D7 d => String "7" (string_of_uint d)
 | D8 d => String "8" (string_of_uint d)
 | D9 d => String "9" (string_of_uint d)
 end.
*)

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
    Let replicateM :=
       fix replicateM' (n: nat) : InModule :=
       match n with
       | 0 => NilInModule
       | S n' => (ConsInModule
       	      	    (Register ^"data"--"0" : Bit 32 <- $0)%kami
       	      	 (ConsInModule
		    (Rule moduleName--"produce"--"0" :=
			Read data_v : Bit 32 <- ^"data"--"0";
			Call consumersend(#data_v); (* method call expr *)
			Write ^"data"--"0" : Bit 32 <- (#data_v + $1);
			Retv (* rule produce *))%kami
       	              (replicateM' n')))
       end.
    Definition mkProducerModule := MODULESTMTS {
         (replicateM numRegs)

    }. (*mkProducer *)

    Definition mkProducer := (mkProducerModule)%kami.
End Producer.
Section ProduceConsume.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable extpcName: string.
    Variable numRegs : nat.

    Definition extpcextCall := MethodSig (extpcName--"extCall") (Bit 32) : Void.

    Let replicateM :=
       fix replicateM' (n: nat) : InModule :=
       match n with
       | 0 => NilInModule
       | S n' => (ConsInModule (Register ^"pcdata"--"0" : Bit 32 <- $0)%kami
       	              (replicateM' n'))
       end.

    Definition mkProduceConsumeModule := MODULESTMTS {

        (replicateM numRegs)
    with (moduleStatement (Rule ^"produce_consume"--"0" :=
        Read data_v : Bit 32 <- ^"pcdata"--"0";
        Call extpcextCall(#data_v); (* method call expr *)
        Write ^"pcdata"--"0" : Bit 32 <- (#data_v + $1);
        Write ^"pcdata"--"0" : Bit 32 <- (#data_v + $2);
        Retv)%kami) (* rule produce_consume *)

    }. (*mkProduceConsume *)

    Definition mkProduceConsume := (mkProduceConsumeModule)%kami.
End ProduceConsume.
