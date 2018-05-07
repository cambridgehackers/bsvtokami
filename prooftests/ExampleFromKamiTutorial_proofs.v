Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Require Import ExampleFromKamiTutorial.

Definition consumer := mkConsumer "c0" "e0".
Definition producer := mkProducer "p0" "c0". 
Definition producerConsumerImpl := (producer ++ consumer)%kami.
Hint Unfold producer : ModuleDefs.
Hint Unfold consumer : ModuleDefs.
Hint Unfold producerConsumerImpl : ModuleDefs.

Definition producer_consumer_ruleMap (_: RegsT): string -> option string :=
  ("p0" -- "produce") |-> ("pc0" -- "produce_consume"); ||.

Definition producer_consumer_regMap (r: RegsT): RegsT.
  (* We are using tactics to build a map from register valuations in [impl] to register valuations in [spec]. *)
  kgetv ("p0" -- "data")%string datav r (Bit 32) (M.empty _: RegsT).
  (* First, extract the value of [impl] register ["data"]. *)
  exact (M.add ("pc0" -- "data")%string (existT _ _ datav) (M.empty _)).
  (* Then, give the corresponding values of all registers for [spec]. *)
Defined.
Hint Unfold producer_consumer_regMap: MethDefs. (* for kdecompose_regMap_init *)

(** The Kami syntax is built by PHOAS, so sometimes we need to prove a PHOAS equivalence for any two variable mappings.  Adding the equivalence lemma to the Coq hint database will allow related features to use it automatically. *)
Lemma impl_ModEquiv:
  ModPhoasWf producerConsumerImpl.
Proof. kequiv. Qed.
Hint Resolve impl_ModEquiv.

(** Now we are ready to prove the refinement! *)
Theorem producer_consumer_refinement:
  producerConsumerImpl <<== mkProduceConsume "pc0" "e0".
Proof.
  kinline_left implInlined.
  (* Inlining: replace internal function calls in [impl]. *)
  kdecompose_nodefs producer_consumer_regMap producer_consumer_ruleMap.
  (* Decomposition: consider all steps [impl] could take, requiring that each be matched appropriately in [spec]. *)

  kinvert.
  (* Inversion on the took-a-step hypothesis, to produce one new subgoal per [impl] rule, etc. *)
  kinv_magic_light.
  (* We have only one case for this example (for the one rule), and it's easy. *)
Qed.
