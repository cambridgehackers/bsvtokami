Require Import Bool String List Arith.
Require Import Kami.All.
Require Import BK.Bsvtokami.
Require Import BK.ExampleFromKamiTutorial.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Theorem produce_consume_refinement:
  TraceInclusion (Foo'mod (mkProduceConsume (mkExtCall)))
                 (flattened_ModWf (module'mkProducerConsumer.wellformed_mkProducerConsumer (mkExtCall))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem consumer_refinement:
  TraceInclusion (Consumer'mod (mkConsumer (mkExtCall))) (flattened_ModWf (module'mkConsumer.wellformed_mkConsumer (mkExtCall))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem flattened_producer_consumer_refinement1:
  TraceInclusion (Producer'mod (mkProducer (mkConsumer (mkExtCall))))
		 (flattened_ModWf (module'mkProducer.wellformed_mkProducer(mkConsumer (mkExtCall)))).
Proof.
  repeat autounfold with ModuleDefs.
    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Theorem spec_impl_refinement:
  TraceInclusion (Foo'mod (mkProduceConsume (mkExtCall)))
                 (flatten_inline_remove (HideMeth (Producer'mod (mkProducerConsumer (mkExtCall))) "send")).
Proof.

  repeat autounfold with ModuleDefs.
  unfold flatten_inline_remove, getHidden, inlineAll_All_mod, getAllRegisters,
         getAllMethods, getAllRules, getRules, getRegisters, getMethods, app.
  unfold inlineAll_All, inlineAll_Meths.
  simpl.
  unfold inlineSingle_Meths_pos, nth_error, map.
  unfold inlineSingle_Meth.
  unfold inlineSingle. simpl.
  unfold inlineAll_Rules, inlineSingle_Rules_pos.
  simpl.
  unfold removeHides.
  simpl.


    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.
