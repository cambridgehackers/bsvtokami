Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* * interface Foo *)
Record Foo := {
    Foo'mod: Mod;
}.

Hint Unfold Foo'mod : ModuleDefs.

(* * interface Consumer *)
Record Consumer := {
    Consumer'mod: Mod;
    Consumer'send : string;
}.

Hint Unfold Consumer'mod : ModuleDefs.
Hint Unfold Consumer'send : ModuleDefs.

(* * interface Producer *)
Record Producer := {
    Producer'mod: Mod;
}.

Hint Unfold Producer'mod : ModuleDefs.

(* * interface ExtCall *)
Record ExtCall := {
    ExtCall'mod: Mod;
    ExtCall'extCall : string;
}.

Hint Unfold ExtCall'mod : ModuleDefs.
Hint Unfold ExtCall'extCall : ModuleDefs.

Module module'mkExtCall.
    Section Section'mkExtCall.
    Variable instancePrefix: string.
    Local Open Scope kami_expr.

    Definition mkExtCallModule: Mod :=
         (BKMODULE {
        Method (instancePrefix--"extCall") (v : (Bit 32)) : Void :=
    (
        Retv    )

    }). (* mkExtCall *)

    Hint Unfold mkExtCallModule : ModuleDefs.
(* Module mkExtCall type Module#(ExtCall) return type ExtCall *)
    Definition mkExtCall := Build_ExtCall mkExtCallModule (instancePrefix--"extCall").
    Hint Unfold mkExtCall : ModuleDefs.
    Hint Unfold mkExtCallModule : ModuleDefs.
    Definition wellformed_mkExtCall : ModWf := @Build_ModWf mkExtCallModule ltac:(intros; repeat autounfold with ModuleDefs; discharge_wf).

    End Section'mkExtCall.
End module'mkExtCall.

Definition mkExtCall := module'mkExtCall.mkExtCall.
Hint Unfold mkExtCall : ModuleDefs.
Hint Unfold module'mkExtCall.mkExtCall : ModuleDefs.
Hint Unfold module'mkExtCall.wellformed_mkExtCall : ModuleDefs.
Hint Unfold module'mkExtCall.mkExtCallModule : ModuleDefs.

Module module'mkConsumer.
    Section Section'mkConsumer.
    Variable instancePrefix: string.
    Variable ext: ExtCall.
    (* instance methods *)
    Let ext'extCall : string := (ExtCall'extCall ext).
    Local Open Scope kami_expr.

    Definition mkConsumerModule: Mod :=
         (BKMODULE {
        Method (instancePrefix--"send") (v : (Bit 32)) : Void :=
    (
BKCall call0 : Void <-  (* translateCall *) ext'extCall ((#v) : Bit 32) ;
        Retv    )

    }). (* mkConsumer *)

    Hint Unfold mkConsumerModule : ModuleDefs.
(* Module mkConsumer type ExtCall -> Module#(Consumer) return type Consumer *)
    Definition mkConsumer := Build_Consumer mkConsumerModule (instancePrefix--"send").
    Hint Unfold mkConsumer : ModuleDefs.
    Hint Unfold mkConsumerModule : ModuleDefs.
    Definition wellformed_mkConsumer : ModWf := @Build_ModWf mkConsumerModule ltac:(intros; repeat autounfold with ModuleDefs; discharge_wf).

    End Section'mkConsumer.
End module'mkConsumer.

Definition mkConsumer := module'mkConsumer.mkConsumer.
Hint Unfold mkConsumer : ModuleDefs.
Hint Unfold module'mkConsumer.mkConsumer : ModuleDefs.
Hint Unfold module'mkConsumer.wellformed_mkConsumer : ModuleDefs.
Hint Unfold module'mkConsumer.mkConsumerModule : ModuleDefs.

Module module'mkProducer.
    Section Section'mkProducer.
    Variable instancePrefix: string.
    Variable consumer: Consumer.
        (* method bindings *)
    Let data : string := instancePrefix--"data".
    (* instance methods *)
    Let consumer'send : string := (Consumer'send consumer).
    Local Open Scope kami_expr.

    Definition mkProducerModule: Mod :=
         (BKMODULE {
        Register data : Bit 32 <-  (* intwidth *) (natToWord 32 0)
    with Rule instancePrefix--"produce" :=
    (
        Read data_v : Bit 32 <- data ;
       BKCall call1 : Void <-  (* translateCall *) consumer'send ((#data_v) : Bit 32) ;
               Write data : Bit 32 <- (#data_v + $$ (* intwidth *) (natToWord 32 1)) ;
        Retv ) (* rule produce *)
    }). (* mkProducer *)

    Hint Unfold mkProducerModule : ModuleDefs.
(* Module mkProducer type Consumer -> Module#(Producer) return type Producer *)
    Definition mkProducer := Build_Producer mkProducerModule.
    Hint Unfold mkProducer : ModuleDefs.
    Hint Unfold mkProducerModule : ModuleDefs.
    Definition wellformed_mkProducer : ModWf := @Build_ModWf mkProducerModule ltac:(intros; repeat autounfold with ModuleDefs; discharge_wf).

    End Section'mkProducer.
End module'mkProducer.

Definition mkProducer := module'mkProducer.mkProducer.
Hint Unfold mkProducer : ModuleDefs.
Hint Unfold module'mkProducer.mkProducer : ModuleDefs.
Hint Unfold module'mkProducer.wellformed_mkProducer : ModuleDefs.
Hint Unfold module'mkProducer.mkProducerModule : ModuleDefs.

Module module'mkProducerConsumer.
    Section Section'mkProducerConsumer.
    Variable instancePrefix: string.
    Variable ext: ExtCall.
        (* method bindings *)
    Let (* action binding *) consumer := mkConsumer (instancePrefix--"consumer") (ext)%bk.
    Let data : string := instancePrefix--"data".
    (* instance methods *)
    Let consumer'send : string := (Consumer'send consumer).
    Local Open Scope kami_expr.

    Definition mkProducerConsumerModule: Mod :=
         (BKMODULE {
        (BKMod (Consumer'mod consumer :: nil))
    with Register data : Bit 32 <-  (* intwidth *) (natToWord 32 0)
    with Rule instancePrefix--"produce" :=
    (
        Read data_v : Bit 32 <- data ;
       BKCall call2 : Void <-  (* translateCall *) consumer'send ((#data_v) : Bit 32) ;
               Write data : Bit 32 <- (#data_v + $$ (* intwidth *) (natToWord 32 1)) ;
        Retv ) (* rule produce *)
    }). (* mkProducerConsumer *)

    Hint Unfold mkProducerConsumerModule : ModuleDefs.
(* Module mkProducerConsumer type ExtCall -> Module#(Producer) return type Producer *)
    Definition mkProducerConsumer := Build_Producer mkProducerConsumerModule.
    Hint Unfold mkProducerConsumer : ModuleDefs.
    Hint Unfold mkProducerConsumerModule : ModuleDefs.
    Definition wellformed_mkProducerConsumer : ModWf := @Build_ModWf mkProducerConsumerModule ltac:(intros; repeat autounfold with ModuleDefs; discharge_wf).

    End Section'mkProducerConsumer.
End module'mkProducerConsumer.

Definition mkProducerConsumer := module'mkProducerConsumer.mkProducerConsumer.
Hint Unfold mkProducerConsumer : ModuleDefs.
Hint Unfold module'mkProducerConsumer.mkProducerConsumer : ModuleDefs.
Hint Unfold module'mkProducerConsumer.wellformed_mkProducerConsumer : ModuleDefs.
Hint Unfold module'mkProducerConsumer.mkProducerConsumerModule : ModuleDefs.

Module module'mkProduceConsume.
    Section Section'mkProduceConsume.
    Variable instancePrefix: string.
    Variable extpc: ExtCall.
        (* method bindings *)
    Let data : string := instancePrefix--"data".
    (* instance methods *)
    Let extpc'extCall : string := (ExtCall'extCall extpc).
    Local Open Scope kami_expr.

    Definition mkProduceConsumeModule: Mod :=
         (BKMODULE {
        Register data : Bit 32 <-  (* intwidth *) (natToWord 32 0)
    with Rule instancePrefix--"produce" :=
    (
        Read data_v : Bit 32 <- data ;
       BKCall call3 : Void <-  (* translateCall *) extpc'extCall ((#data_v) : Bit 32) ;
               Write data : Bit 32 <- (#data_v + $$ (* intwidth *) (natToWord 32 1)) ;
        Retv ) (* rule produce *)
    }). (* mkProduceConsume *)

    Hint Unfold mkProduceConsumeModule : ModuleDefs.
(* Module mkProduceConsume type ExtCall -> Module#(Foo) return type Foo *)
    Definition mkProduceConsume := Build_Foo mkProduceConsumeModule.
    Hint Unfold mkProduceConsume : ModuleDefs.
    Hint Unfold mkProduceConsumeModule : ModuleDefs.
    Definition wellformed_mkProduceConsume : ModWf := @Build_ModWf mkProduceConsumeModule ltac:(intros; repeat autounfold with ModuleDefs; discharge_wf).

    End Section'mkProduceConsume.
End module'mkProduceConsume.

Definition mkProduceConsume := module'mkProduceConsume.mkProduceConsume.
Hint Unfold mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.wellformed_mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.mkProduceConsumeModule : ModuleDefs.

