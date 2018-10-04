Require Import Bool String List Arith.
Require Import Kami.All.
Require Import BK.Bsvtokami.
Require Import BK.ExampleFromKamiTutorial.

Require Import FunctionalExtensionality.

Set Implicit Arguments.



Check mkExtCall.
Check mkConsumer.
Check mkProducer.
Check mkProduceConsume.

Definition extcall := mkExtCall "e0".
Definition consumer := mkConsumer "c0" extcall.
Definition producer := mkProducer "p0" consumer.
Hint Unfold extcall : ModuleDefs.
Hint Unfold producer : ModuleDefs.
Hint Unfold consumer : ModuleDefs.

Definition producerModules := (Producer'mod producer).
Hint Unfold producerModules : ModuleDefs.

Definition producerConsumer := mkProduceConsume "pc0" extcall.
Hint Unfold producerConsumer : ModuleDefs.
Definition producerConsumerModules := Foo'mod producerConsumer.
Hint Unfold producerConsumerModules : ModuleDefs.

Check producerModules.
Compute producerModules.
Check producerConsumerModules.
Compute producerConsumerModules.

Hint Unfold Foo'mod : ModuleDefs.
Hint Unfold mkExtCall : ModuleDefs.
Hint Unfold ExtCall'mod : ModuleDefs.
Hint Unfold ExtCall'extCall : ModuleDefs.

Hint Unfold makeBKModule : ModuleDefs.
Hint Unfold makeBKModule' : ModuleDefs.
Hint Unfold concatModules : ModuleDefs.
Hint Unfold module'mkReg.reg : ModuleDefs.
Hint Unfold app : ModuleDefs. (* questionable *)

(** Now we are ready to prove the refinement! *)
Theorem producer_consumer_refinement1:
  producerConsumerModules <<== producerConsumerModules.
Proof.

  repeat autounfold with ModuleDefs.
  kinline_left pcImpl.


  (* Inlining: replace internal function calls in [impl]. *)
  kdecompose_nodefs pc_regMap pc_ruleMap.
  (* Decomposition: consider all steps [impl] could take, requiring that each be matched appropriately in [spec]. *)

  kinvert.
  (* Inversion on the took-a-step hypothesis, to produce one new subgoal per [impl] rule, etc. *)
  kinv_magic_light.
  apply H0.
  (* We have only one case for this example (for the one rule), and it's easy. *)
Qed.

