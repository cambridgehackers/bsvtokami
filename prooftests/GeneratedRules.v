Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Section Consumer.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable extName: string.
    Definition extextCall := MethodSig (extName--"extCall") (Bit 32) : Void.
    Definition mkConsumerModule := (BKMODULE {

    Method ^"send" (v: (Bit 32)) : Void := 
        Call extextCall(#v); (* method call expr *)
        Retv

    }). (*mkConsumer *)

    Definition mkConsumer := (mkConsumerModule)%kami.
End Consumer.
Section Producer.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable consumerName: string.
    Definition consumersend := MethodSig (consumerName--"send") (Bit 32) : Void.
    Definition mkProducerModule := (BKMODULE {

        (BKElts
      ((fix loopM' (limit: nat) (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in STMTSR {
    Register ^"datafoo" : Bit 32 <- $0
    with Rule ^"produce" :=
        Read datafoo_v : Bit 32 <- ^"datafoo";
        Call consumersend(#datafoo_v); (* method call expr *)
        Write ^"datafoo" : Bit 32 <- (#datafoo_v + $10);
        Retv (* rule produce *)

          }
          (loopM' limit m')
        end)
        10 10))
    }). (*mkProducer *)

    Definition mkProducer := (mkProducerModule)%kami.
End Producer.
Section ProduceConsume.
    Variable moduleName: string.
    Local Notation "^ s" := (moduleName -- s) (at level 0).
    Variable extpcName: string.
    Definition extpcextCall := MethodSig (extpcName--"extCall") (Bit 32) : Void.
    Definition mkProduceConsumeModule := (BKMODULE {

        (BKElts
      ((fix loopM' (limit: nat) (m: nat): InBKModule :=
        match m with
        | 0 => NilInBKModule
        | S m' =>
          let i := limit - m
          in STMTSR {
    Register ^"data" : Bit 32 <- $0
    with Rule ^"produce" :=
        Read data_v : Bit 32 <- ^"data";
        Write ^"data" : Bit 32 <- (#data_v + $10);
        Call extpcextCall(#data_v); (* method call expr *)
        Retv (* rule produce *)

          }
          (loopM' limit m')
        end)
        10 10))
    }). (*mkProduceConsume *)

    Definition mkProduceConsume := (mkProduceConsumeModule)%kami.
End ProduceConsume.
