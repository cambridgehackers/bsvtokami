Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Consumer *)
Definition Consumer := string.
(* * interface Producer *)
Definition Producer := string.
(* * interface ExtCall *)
Definition ExtCall := string.
Section Consumer.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable ext: ExtCall.
    Definition extextCall := MethodSig (ext--"extCall") (Bit 32) : Void.
        Definition mkConsumerModule := 
        (BKMODULE {
           Method ^"send" (v: (Bit 32)) : Void := 
        Call extextCall(#v);
        Retv

    }). (* mkConsumer *)

    Definition mkConsumer := (mkConsumerModule)%kami.
End Consumer.
Section Producer.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable consumer: Consumer.
    Variable numRules: nat.
    Definition consumersend := MethodSig (consumer--"send") (Bit 32) : Void.
        Definition mkProducerModule := 
        (BKMODULE {
               (BKElts
      (let limit : nat := numRules
       in let moduleName : string := moduleName--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let moduleName := moduleName--(toBinaryString i)
          in LOOP {
        Register ^"datafoo" : Bit 32 <- $0
        with Rule ^"produce" :=
        Read datafoo_v : Bit 32 <- ^"datafoo";
               Call consumersend(#datafoo_v);
               Write ^"datafoo" : Bit 32 <- (#datafoo_v + $10);
        Retv (* rule produce *)

          }
          (loopM' m')
        end)
        numRules)))
    }). (* mkProducer *)

    Definition mkProducer := (mkProducerModule)%kami.
End Producer.
Section ProduceConsume.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable extpc: ExtCall.
    Variable numRules: nat.
    Definition extpcextCall := MethodSig (extpc--"extCall") (Bit 32) : Void.
        Definition mkProduceConsumeModule := 
        (BKMODULE {
               (BKElts
      (let limit : nat := numRules
       in let moduleName : string := moduleName--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let moduleName := moduleName--(toBinaryString i)
          in LOOP {
        Register ^"data" : Bit 32 <- $0
        with Rule ^"produce" :=
        Read data_v : Bit 32 <- ^"data";
               Write ^"data" : Bit 32 <- (#data_v + $10);
               Call extpcextCall(#data_v);
        Retv (* rule produce *)

          }
          (loopM' m')
        end)
        numRules)))
    }). (* mkProduceConsume *)

    Definition mkProduceConsume := (mkProduceConsumeModule)%kami.
End ProduceConsume.
