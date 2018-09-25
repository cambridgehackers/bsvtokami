Require Import Bool String List Arith.
Require Import Omega.
Require Import micromega.Lia.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Foo *)
Record Foo := {
    Foo'modules: Modules;
}.

(* * interface Consumer *)
Record Consumer := {
    Consumer'modules: Modules;
    Consumer'send : string;
}.

(* * interface Producer *)
Record Producer := {
    Producer'modules: Modules;
}.

(* * interface ExtCall *)
Record ExtCall := {
    ExtCall'modules: Modules;
    ExtCall'extCall : string;
}.

Module module'mkExtCall.
    Section Section'mkExtCall.
    Variable instancePrefix: string.
    Definition mkExtCallModule: Modules :=
         (BKMODULE {
        Method instancePrefix--"extCall" (v : (Bit 32)) : Void :=
    (
        Retv    )

    }). (* mkExtCall *)

(* Module mkExtCall type Module#(ExtCall) return type ExtCall *)
    Definition mkExtCall := Build_ExtCall mkExtCallModule%kami (instancePrefix--"extCall").
    End Section'mkExtCall.
End module'mkExtCall.

Definition mkExtCall := module'mkExtCall.mkExtCall.
Hint Unfold mkExtCall : ModuleDefs.
Hint Unfold module'mkExtCall.mkExtCall : ModuleDefs.
Hint Unfold module'mkExtCall.mkExtCallModule : ModuleDefs.

Module module'mkConsumer.
    Section Section'mkConsumer.
    Variable instancePrefix: string.
    Variable ext: ExtCall.
    (* instance methods *)
    Let extextCall : string := (ExtCall'extCall ext).
    Definition mkConsumerModule: Modules :=
         (BKMODULE {
        Method instancePrefix--"send" (v : (Bit 32)) : Void :=
    (
CallM call0 : Void <-  extextCall (#v : Bit 32);
        Retv    )

    }). (* mkConsumer *)

(* Module mkConsumer type ExtCall -> Module#(Consumer) return type Consumer *)
    Definition mkConsumer := Build_Consumer mkConsumerModule%kami (instancePrefix--"send").
    End Section'mkConsumer.
End module'mkConsumer.

Definition mkConsumer := module'mkConsumer.mkConsumer.
Hint Unfold mkConsumer : ModuleDefs.
Hint Unfold module'mkConsumer.mkConsumer : ModuleDefs.
Hint Unfold module'mkConsumer.mkConsumerModule : ModuleDefs.

Module module'mkProducer.
    Section Section'mkProducer.
    Variable instancePrefix: string.
    Variable consumer: Consumer.
    (* let bindings *)
    Let initval : ConstT (Bit 32) := ($$(natToWord 32 0))%kami.
        (* method bindings *)
    Let data := mkReg (Bit 32) (instancePrefix--"data") (initval)%bk.
    Let data_read : string := (Reg'_read data).
    Let data_write : string := (Reg'_write data).
    (* instance methods *)
    Let consumersend : string := (Consumer'send consumer).
    Definition mkProducerModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules data :: nil))
    with Rule instancePrefix--"produce" :=
    (
        CallM data_v : Bit 32 (* regRead *) <- data_read();
       CallM call1 : Void <-  consumersend (#data_v : Bit 32);
               CallM data_write ( (#data_v + $1) : Bit 32 );
        Retv ) (* rule produce *)
    }). (* mkProducer *)

(* Module mkProducer type Consumer -> Module#(Producer) return type Producer *)
    Definition mkProducer := Build_Producer mkProducerModule%kami.
    End Section'mkProducer.
End module'mkProducer.

Definition mkProducer := module'mkProducer.mkProducer.
Hint Unfold mkProducer : ModuleDefs.
Hint Unfold module'mkProducer.mkProducer : ModuleDefs.
Hint Unfold module'mkProducer.mkProducerModule : ModuleDefs.

Module module'mkProduceConsume.
    Section Section'mkProduceConsume.
    Variable instancePrefix: string.
    Variable extpc: ExtCall.
    (* let bindings *)
    Let initval : ConstT (Bit 32) := ($$(natToWord 32 0))%kami.
        (* method bindings *)
    Let data := mkReg (Bit 32) (instancePrefix--"data") (initval)%bk.
    Let data_read : string := (Reg'_read data).
    Let data_write : string := (Reg'_write data).
    (* instance methods *)
    Let extpcextCall : string := (ExtCall'extCall extpc).
    Definition mkProduceConsumeModule: Modules :=
         (BKMODULE {
        (BKMod (Reg'modules data :: nil))
    with Rule instancePrefix--"produce_consume" :=
    (
        CallM data_v : Bit 32 (* regRead *) <- data_read();
       CallM call2 : Void <-  extpcextCall (#data_v : Bit 32);
               CallM data_write ( (#data_v + $1) : Bit 32 );
        Retv ) (* rule produce_consume *)
    }). (* mkProduceConsume *)

(* Module mkProduceConsume type ExtCall -> Module#(Foo) return type Foo *)
    Definition mkProduceConsume := Build_Foo mkProduceConsumeModule%kami.
    End Section'mkProduceConsume.
End module'mkProduceConsume.

Definition mkProduceConsume := module'mkProduceConsume.mkProduceConsume.
Hint Unfold mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.mkProduceConsumeModule : ModuleDefs.

