Require Import Bool String List Arith.
Require Import Kami.All.
Require Import BK.Bsvtokami.
Require Import BK.ExampleFromKamiTutorial.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

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

Ltac do_inlining :=
  repeat autounfold with ModuleDefs;
  unfold flatten_inline_remove, getHidden, inlineAll_All_mod, getAllRegisters,
         getAllMethods, getAllRules, getRules, getRegisters, getMethods, app;
  unfold inlineAll_All, inlineAll_Meths;
  simpl;
  unfold inlineSingle_Meths_pos, nth_error, map;
  unfold inlineSingle_Meth;
  unfold inlineSingle; simpl;
  unfold inlineAll_Rules, inlineSingle_Rules_pos;
  simpl;
  unfold removeHides;
  simpl.

Theorem spec_impl_refinement:
  TraceInclusion (Foo'mod (mkProduceConsume (mkExtCall)))
                 (flatten_inline_remove (HideMeth (Producer'mod (mkProducerConsumer (mkExtCall))) "send")).
Proof.

  do_inlining.

    unfold TraceInclusion.
  intros.
  exists o1, ls1.
  repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
Qed.

Check flatten_inline_remove.

Definition spec := (Foo'mod (mkProduceConsume (mkExtCall))).
Definition impl := Base (flatten_inline_remove (HideMeth (Producer'mod (mkProducerConsumer (mkExtCall))) "send")).
Hint Unfold spec : ModuleDefs.
Hint Unfold impl : ModuleDefs.
Check spec.
Check impl.

Definition mySimRel (iregs sregs: RegsT) :=
  (getKindAttr sregs = ("data", SyntaxKind (Bit 32)) :: nil)
   /\ (getKindAttr iregs = ("data", SyntaxKind (Bit 32)) :: nil)
   /\ Forall2 (fun (sreg ireg: RegT) => (fst sreg) = (fst ireg)) sregs iregs.

Print makeBKModule.

Definition flattened_spec := (BaseMod
        (("data",
         existT optConstFullT (SyntaxKind (Bit 32))
           (Some (makeConst (ConstBit $0)))) :: nil)
        (("produce",
         fun ty : Kind -> Type =>
         (Read ret : Bit 32 <- "data" ;
          LETA _ : Void <-
          LET v : Bit 32 <- Var ty (SyntaxKind (Bit 32)) ret ;
          BKCall _ : Void <- "extCall"
          (Var ty (SyntaxKind (Bit 32)) v : Bit 32) ;
          Ret Const ty (ConstBit (wzero 0)) ;
          Write "data" : Bit 32 <-
          Var ty (SyntaxKind (Bit 32)) ret + Const ty (ConstBit $1) ;
          Ret Const ty (ConstBit (wzero 0)))%kami_action) :: nil) nil).



Definition flattened_impl :=
(BaseMod
        (("data",
         existT optConstFullT (SyntaxKind (Bit 32))
           (Some (makeConst (ConstBit $0)))) :: nil)
        (("produce",
         fun ty : Kind -> Type =>
         (Read ret : Bit 32 <- "data" ;
          LETA _ : Void <-
          LET v : Bit 32 <- Var ty (SyntaxKind (Bit 32)) ret ;
          BKCall _ : Void <- "extCall"
          (Var ty (SyntaxKind (Bit 32)) v : Bit 32) ;
          Ret Const ty (ConstBit (wzero 0)) ;
          Write "data" : Bit 32 <-
          Var ty (SyntaxKind (Bit 32)) ret + Const ty (ConstBit $1) ;
          Ret Const ty (ConstBit (wzero 0)))%kami_action) :: nil) nil).

Search (BaseModule -> BaseModuleWf).
Definition flattened_spec_wf := {| baseModule := flattened_spec; wfBaseModule := ltac:(discharge_wf) |}.
Definition flattened_impl_wf := {| baseModule := flattened_impl; wfBaseModule := ltac:(discharge_wf) |}.

Theorem regs_ok:
  forall x,
  fst x = "data"
  /\ projT1 (snd x) = SyntaxKind (Bit 32)
  /\ exists rspec : list RegT,
  Forall2
    (fun (o' : RegT) (r : string * {x1 : FullKind & option (ConstFullT x1)}) =>
     fst o' = fst r /\
     (exists pf : projT1 (snd o') = projT1 (snd r),
        match projT2 (snd r) with
        | Some x1 =>
            match pf in (_ = Y) return (fullType type Y) with
            | eq_refl => projT2 (snd o')
            end = evalConstFullT x1
        | None => True
        end)) rspec
    (("data", existT optConstFullT (SyntaxKind (Bit 32)) (Some (makeConst (ConstBit $0))))
     :: nil) /\ mySimRel (x :: nil) rspec.

Proof.
Admitted.

Theorem nodup_oimp:
  forall oImp : RegsT, getKindAttr oImp = ("data", SyntaxKind (Bit 32)) :: nil -> NoDup (map fst oImp).
Proof.
Admitted.


Theorem spec_spec_flattened_simulation:
TraceInclusion
  (Base
     flattened_spec_wf)
  (Base
     flattened_spec_wf).
Proof.
  unfold flattened_impl_wf.
  unfold flattened_impl.
  unfold flattened_spec_wf.
  unfold flattened_spec.
  pose proof (wfBaseModule flattened_impl_wf) as wfImp.
  discharge_simulationGeneral mySimRel (NoDup (map fst (getRegisters flattened_spec_wf))).
  + discharge_NoSelfCall.
  + unfold mySimRel in H. apply H.
  + unfold mySimRel in H. apply H.
  + intros. apply regs_ok.
  + unfold mySimRel. econstructor.
    unfold mySimRel in H1.
    destruct H1. destruct H2. split.
    * split.
      ** apply H1.
      ** split.
         *** rewrite <- H2. rewrite <- getKindAttr_doUpdRegs. econstructor.
          ++ apply nodup_oimp. apply H2.
          ++ econstructor. eauto.
             econstructor.
          ++ intros. rewrite H2. econstructor. admit.
         *** admit.
    * admit. (* this one seems wrong *)
Qed.

Theorem spec_impl_flattened_simulation:
TraceInclusion
  (Base
     flattened_impl_wf)
  (Base
     flattened_spec_wf).
Proof.
  unfold flattened_impl_wf.
  unfold flattened_impl.
  unfold flattened_spec_wf.
  unfold flattened_spec.
  pose proof (wfBaseModule flattened_impl_wf) as wfImp.
  discharge_simulationGeneral mySimRel (NoDup (map fst (getRegisters flattened_impl_wf))).
  + discharge_NoSelfCall.
  + unfold mySimRel in H. apply H.
  + unfold mySimRel in H. apply H.
  + intros. apply regs_ok.
  + unfold mySimRel. econstructor.
    unfold mySimRel in H1.
    destruct H1. destruct H2. split.
    * split.
      ** apply H1.
      ** split.
         *** rewrite <- H2. rewrite <- getKindAttr_doUpdRegs. econstructor.
          ++ apply nodup_oimp. apply H2.
          ++ econstructor. eauto.
             econstructor.
          ++ intros. rewrite H2. econstructor. admit.
         *** admit.
    * admit. (* this one seems wrong *)
Qed.

Theorem spec_impl_discharge_simulation:
  TraceInclusion impl spec.
Proof.
  (* do_inlining. *)
  unfold spec.
  unfold mkProduceConsume.
  unfold module'mkProduceConsume.mkProduceConsume.
  unfold Foo'mod.
  unfold module'mkProduceConsume.mkProduceConsumeModule.
  unfold makeBKModule.
  unfold makeBKModule'.
  unfold concatModules.
  repeat autounfold with ModuleDefs.

  do_inlining.
  pose proof (wfBaseModule imp) as wfImp.

    apply simulationGeneral with (simRel := mySimRel). auto; simpl; intros.
  discharge_simulationGeneral simRel (NoDup (map fst (getRegisters impl))).
Qed.
