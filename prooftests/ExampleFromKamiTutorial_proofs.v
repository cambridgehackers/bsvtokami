Require Import Bool String List Arith.
Require Import Kami.All.
Require Import BK.Bsvtokami.
Require Import BK.ExampleFromKamiTutorial.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

Theorem producer_consumer_refinement2 (prefix: string):
  TraceInclusion (Consumer'mod (mkConsumer prefix (mkExtCall (prefix--"ext")))) (flattened_ModWf (module'mkConsumer.wellformed_mkConsumer prefix (mkExtCall (prefix--"ext")))).
Proof.
  repeat autounfold with ModuleDefs.
  apply TraceInclusion_flatten_r.
Qed.
