Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface SubConsumer *)
Record SubConsumerInterface := {
    SubConsumer'foo : string;
}.
Definition SubConsumer := string.
(* * interface Consumer *)
Record ConsumerInterface := {
    Consumer'send : string;
}.
Definition Consumer := string.
(* * interface Producer *)
Record ProducerInterface := {
}.
Definition Producer := string.
(* * interface ExtCall *)
Record ExtCallInterface := {
    ExtCall'extCall : string;
}.
Definition ExtCall := string.
Section Consumer.
    Variable instancePrefix: string.
    Variable ext: ExtCall.
    Let extextCall := MethodSig (ext--"extCall") (Bit 32) : Void.
        Definition mkConsumerModule :=
        (BKMODULE {
           Method instancePrefix--"send" (v: (Bit 32)) : Void :=
        Call extextCall(#v);
        Retv

    }). (* mkConsumer *)

    Definition mkConsumer := (mkConsumerModule)%kami.
End Consumer.
Section Producer.
    Variable instancePrefix: string.
    Variable consumer: Consumer.
    Variable numRules: nat.
    Let consumersend := MethodSig (consumer--"send") (Bit 32) : Void.
        Definition mkProducerModule :=
        (BKMODULE {
               (BKBlock
      (let limit : nat := numRules
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        (BKBlock (
        let datafoo : string := instancePrefix--"datafoo" in
        BKSTMTS {
        Register datafoo : Bit 32 <- $0
        with Rule instancePrefix--"produce" :=
        Read datafoo_v : Bit 32 <- datafoo;
               Call consumersend(#datafoo_v);
               Write datafoo : Bit 32 <- (#datafoo_v + $10);
        Retv (* rule produce *)
        }))
        (loopM' m')
        end)
        numRules)))
    }). (* mkProducer *)

    Definition mkProducer := (mkProducerModule)%kami.
End Producer.
Section ManyConsumer.
    Variable instancePrefix: string.
    Variable ext: ExtCall.
    Variable numRules: nat.
        Definition mkManyConsumerModule :=
        (BKMODULE {
               (BKBlock
      (let limit : nat := numRules
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        (BKBlock (
        let c := mkConsumer (instancePrefix--"c") in
        let datafoo : string := instancePrefix--"datafoo" in
        BKSTMTS {
        (BKMod (mkConsumer c :: nil))
        with Register datafoo : Bit 32 <- $0
        with Rule instancePrefix--"produce" :=
        Read datafoo_v : Bit 32 <- datafoo;
               Call csend(#datafoo_v);
               Write datafoo : Bit 32 <- (#datafoo_v + $10);
        Retv (* rule produce *)
        }))
        (loopM' m')
        end)
        numRules)))
    }). (* mkManyConsumer *)

    Definition mkManyConsumer := (mkManyConsumerModule)%kami.
End ManyConsumer.
Section ProduceConsume.
    Variable instancePrefix: string.
    Variable extpc: ExtCall.
    Variable numRules: nat.
    Let extpcextCall := MethodSig (extpc--"extCall") (Bit 32) : Void.
        Definition mkProduceConsumeModule :=
        (BKMODULE {
               (BKBlock
      (let limit : nat := numRules
       in let instancePrefix : string := instancePrefix--"i"
      in ((fix loopM' (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in let instancePrefix := instancePrefix--(toBinaryString i)
          in ConsInBKModule
        (BKBlock (
        let data : string := instancePrefix--"data" in
        BKSTMTS {
        Register data : Bit 32 <- $0
        with Rule instancePrefix--"produce" :=
        Read data_v : Bit 32 <- data;
               Write data : Bit 32 <- (#data_v + $10);
               Call extpcextCall(#data_v);
        Retv (* rule produce *)
        }))
        (loopM' m')
        end)
        numRules)))
    }). (* mkProduceConsume *)

    Definition mkProduceConsume := (mkProduceConsumeModule)%kami.
End ProduceConsume.
