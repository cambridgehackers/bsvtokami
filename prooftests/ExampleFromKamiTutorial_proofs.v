Require Import Bool String List Arith.
Require Import Kami.
Require Import Lib.Indexer.
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

Definition producerModules := (Producer'modules producer).
Hint Unfold producerModules : ModuleDefs.

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
  ModPhoasWf producerModules.
Proof. kequiv. Qed.
Hint Resolve impl_ModEquiv.

Definition producerConsumer := mkProduceConsume "pc0" extcall.
Hint Unfold producerConsumer : ModuleDefs.
Definition producerConsumerModules := Foo'modules producerConsumer.
Hint Unfold producerConsumerModules : ModuleDefs.

Lemma pc_ModEquiv:
  ModPhoasWf producerConsumerModules.
Proof. kequiv. Qed.
Hint Resolve pc_ModEquiv.

Check producerModules.
Compute producerModules.
Compute getDefsBodies producerModules.
Check producerConsumerModules.
Compute producerConsumerModules.
Compute getDefsBodies producerConsumerModules.
Compute getCalls producerConsumerModules.
Compute getRules producerConsumerModules.
Compute getRegInits producerConsumerModules.
Definition ipc := fst (inlineF producerConsumerModules).
Hint Unfold ipc : ModuleDefs.
Lemma impl_IPC:
  ModPhoasWf ipc.
Proof. kequiv. Qed.
Hint Resolve impl_IPC.

Compute getDefsBodies ipc.

Hint Unfold getDefsBodies : FOODEF.

Definition pc_regMap1 (r: RegsT): RegsT.
  (* We are using tactics to build a map from register valuations in [impl] to register valuations in [spec]. *)
  kgetv ("p0" -- "data"--"reg")%string datav r (Bit 32) (M.empty _: RegsT).
  (* First, extract the value of [impl] register ["data"]. *)
  exact (M.add ("pc0" -- "data"--"reg")%string (existT _ _ datav) (M.empty _)).
  (* Then, give the corresponding values of all registers for [spec]. *)
Defined.
Definition pc_regMap (r: RegsT): RegsT := r.
Hint Unfold pc_regMap: MethDefs. (* for kdecompose_regMap_init *)
Compute pc_regMap.

Definition pc_ruleMap (_: RegsT): string -> option string :=
  ("pc0" -- "produce_consume") |-> ("pc0" -- "produce_consume"); ||.

Hint Unfold Foo'modules : ModuleDefs.
Hint Unfold mkExtCall : ModuleDefs.


Compute ipc.

Definition ipc1 := Mod
         [("reg.data.pc0"
           :: RegInitCustom
                (existT ConstFullT (SyntaxKind (Bit 32))
                   (SyntaxConst WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0)))%struct]
         [("produce_consume.pc0"
           :: (fun ty : Kind -> Type =>
               (LET _ : Bit 0 <- $$ (WO);
                Read x0 : Bit 32 <- "reg.data.pc0";
                LET x1 : Bit 32 <- # (x0);
                CallM _ : Bit 0 <- "extCall.e0" (# (x1) : Bit 32);
                LET x3 : Bit 32 <- # (x1) + $$ (WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1);
                Write "reg.data.pc0" : Bit 32 <- # (x3); LET _ : Bit 0 <- $$ (WO); Ret $$ (WO))%kami_action))%struct] nil.
Check ipc1.

(** Now we are ready to prove the refinement! *)
Theorem producer_consumer_refinement0:
  ipc1 <<== ipc1.
Proof.
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

Lemma foo_PHOAS:
ModPhoasWf (fst (inlineF producerConsumerModules)).
Proof. kequiv. Qed.
Hint Resolve impl_ModEquiv.
Hint Unfold mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.mkProduceConsume : ModuleDefs.
Hint Unfold module'mkProduceConsume.mkProduceConsumeModule : ModuleDefs.
Hint Unfold makeBKModule : ModuleDefs.
Hint Unfold makeBKModule' : ModuleDefs.
Hint Unfold concatModules : ModuleDefs.
Hint Unfold Reg'modules : ModuleDefs.
Hint Unfold mkReg : ModuleDefs.
Hint Unfold module'mkReg.mkReg : ModuleDefs.
Hint Unfold module'mkReg.mkRegModule : ModuleDefs.
Hint Unfold module'mkReg.reg : ModuleDefs.
Hint Unfold Reg'_write : ModuleDefs.
Hint Unfold Reg'_read : ModuleDefs.
Hint Unfold app : ModuleDefs. (* questionable *)
Hint Unfold getDefsBodies : ModuleDefs.

(** Now we are ready to prove the refinement! *)
Theorem producer_consumer_refinement1:
  producerConsumerModules <<== fst (inlineF producerConsumerModules).
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

