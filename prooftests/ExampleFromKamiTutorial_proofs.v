Require Import Bool String List Arith.
Require Import Kami.All.
Require Import BK.Bsvtokami.
Require Import BK.ExampleFromKamiTutorial.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Theorem produce_consume_refinement (prefix: string):
  TraceInclusion (Foo'mod (mkProduceConsume prefix (mkExtCall (prefix--"ext"))))
                 (flattened_ModWf (module'mkProducerConsumer.wellformed_mkProducerConsumer prefix (mkExtCall (prefix--"ext")))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem consumer_refinement (prefix: string):
  TraceInclusion (Consumer'mod (mkConsumer prefix (mkExtCall (prefix--"ext")))) (flattened_ModWf (module'mkConsumer.wellformed_mkConsumer prefix (mkExtCall (prefix--"ext")))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem flattened_producer_consumer_refinement1 (prefix: string):
  TraceInclusion (Producer'mod (mkProducer prefix (mkConsumer (prefix--"c0") (mkExtCall (prefix--"ext")))))
		 (flattened_ModWf (module'mkProducer.wellformed_mkProducer prefix(mkConsumer (prefix--"c0") (mkExtCall (prefix--"ext"))))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem producer_consumer_refinement (prefix: string):
  TraceInclusion (Producer'mod (mkProducerConsumer prefix (mkExtCall (prefix--"ext"))))
                 (flattened_ModWf (module'mkProducerConsumer.wellformed_mkProducerConsumer prefix (mkExtCall (prefix--"ext")))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem produce_consume_refinement (prefix: string):
  TraceInclusion (Foo'mod (mkProduceConsume prefix (mkExtCall (prefix--"ext"))))
                 (flattened_ModWf (module'mkProducerConsumer.wellformed_mkProducerConsumer prefix (mkExtCall (prefix--"ext")))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.
