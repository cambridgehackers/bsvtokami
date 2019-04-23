Require Import Kami.Syntax Lib.Fold.

Import ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutEq.
Require Import RelationClasses Setoid Morphisms.
Require Import ZArith.
Require Import Kami.Properties.

(* Definition getBaseModuleWf (bm : BaseModule) := @Build_BaseModuleWf bm ltac:(discharge_wf). *)

(* included from Properties.v *)

Section SimulationGen.
  Variable imp spec: BaseModuleWf.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp oImp' aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel oImp' oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel oImp' oSpec')).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp oImp' sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      UpdRegs [uImp] oImp oImp' ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
              exists oSpec',
                UpdRegs [uSpec] oSpec oSpec' /\
                simRel oImp' oSpec'.

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Lemma SubstepsSingle o l:
    Substeps imp o l ->
    length l <= 1.
  Proof.
    induction 1; simpl; auto; intros; subst.
    - destruct ls; simpl in *; auto; simpl in *.
      assert (sth1: length ls = 0) by (simpl in *; Omega.omega).
      rewrite length_zero_iff_nil in sth1; subst; simpl in *.
      specialize (HNoRle p (or_introl eq_refl)).
      specialize (HDisjRegs p (or_introl eq_refl)).
      repeat destruct p; simpl in *.
      destruct r0; simpl in *; [tauto|].
      inv H; [discriminate|].
      destruct fb; simpl in *.
      destruct (@notRuleMeth _ _ _ _ _ _ _ _ _ _ _ _ _ _ HInRules HAction HInMeths HAction0) as [k [in1 in2]].
      specialize (HDisjRegs k).
      inv HLabel.
      tauto.
    - destruct ls; simpl in *; auto; simpl in *.
      assert (sth1: length ls = 0) by (simpl in *; Omega.omega).
      rewrite length_zero_iff_nil in sth1; subst; simpl in *.
      specialize (HDisjRegs p (or_introl eq_refl)).
      repeat destruct p; simpl in *.
      inv H.
      + inv HLabel; simpl in *.
        inv HSubstep; try congruence.
        destruct fb.
        destruct (@notRuleMeth _ _ _ _ _ _ _ _ _ _ _ _ _ _ HInRules HAction0 HInMeths HAction) as [k [in1 in2]].
        specialize (HDisjRegs k).
        tauto.
      + destruct ls; [| discriminate].
        inv HLabel.
        destruct fb.
        destruct fb0.
        destruct (@notMethMeth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HInMeths HAction HInMeths0 HAction0) as [k [in1 in2]].
        specialize (HDisjRegs k).
        tauto.
  Qed.
        
  Theorem simulationGen:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    idtac "simulationGen".
    pose proof (wfBaseModule imp) as wfImp.
    pose proof (wfBaseModule spec) as wfSpec.
    inv wfImp.
    inv wfSpec.
    dest.
    idtac "StepSimulation".
    apply StepSimulation with (simRel := simRel); auto; simpl; intros.
    inv H9.
    idtac "SubstepsSingle".
    pose proof (SubstepsSingle HSubsteps) as sth.
    destruct lImp; [tauto| simpl in *].
    destruct lImp; simpl in *; [| Omega.omega].
    repeat destruct p; simpl in *.
    inv HSubsteps; inv HLabel; simpl in *.
    - destruct (@simulationRule _ _ _ _ _ _ _ HInRules HAction H11 _ H12); dest; subst.
      exists nil, oSpec.
      split.
      + constructor; auto; simpl in *.
        * constructor 1; auto.
          eapply simRelGood; eauto.
        * unfold MatchingExecCalls_Base, getNumCalls, getNumExecs; intros; simpl.
          Omega.omega.
      + simpl.
        split.
        * unfold UpdRegs; repeat split; auto; intros.
          right; split; try intro; simpl in *; auto.
          dest; auto.
        * split; auto.
          unfold WeakInclusion; simpl; intros.
          unfold getListFullLabel_diff; simpl.
          split; intros; dest; auto.
          tauto.
      + exists [(x2, (Rle x, cs))], x3; simpl.
        split.
        * constructor; auto.
          -- econstructor 2; eauto.
             ++ eapply WfActionT_ReadsWellDefined; eauto.
             ++ eapply WfActionT_WritesWellDefined; eauto.
             ++ simpl; intros; tauto.
             ++ constructor 1; auto.
                eapply simRelGood; eauto.
          -- unfold MatchingExecCalls_Base; unfold getNumCalls, getNumExecs; simpl; intros.
             rewrite app_nil_r.
             assert (th1: forall x, (x = 0)%Z -> (x <= 0)%Z) by (intros; Omega.omega).
             apply th1; clear th1.
             eapply NoSelfCallRule_Impl; eauto.
        * split; auto.
          split; auto.
          unfold WeakInclusion; simpl; intros.
          split; intros; auto.
          exists rn.
          left; auto.
    - destruct fb.
      destruct (@simulationMeth _ _ _ _ _ _ _ _ _ _ HInMeths HAction H11 _ H12); dest; subst.
      exists [(x2, (Meth (fn, existT _ x (argV, retV)), cs))], x3; simpl.
      split.
      * constructor; auto.
        -- econstructor 3; eauto.
           ++ eapply WfActionT_ReadsWellDefined; eauto.
           ++ eapply WfActionT_WritesWellDefined; eauto.
           ++ simpl; intros; tauto.
           ++ constructor 1; auto.
              eapply simRelGood; eauto.
        -- unfold MatchingExecCalls_Base; unfold getNumCalls, getNumExecs; simpl; intros.
           rewrite app_nil_r.
           assert (th1: forall x, (x = 0)%Z -> (x <= 0)%Z) by (intros; Omega.omega).
           match goal with
           | |- (_ <= if ?P then _ else _)%Z => destruct P; subst; simpl in *
           end.
           ++ assert (th2: forall x, (x = 0)%Z -> (x <= 1)%Z) by (intros; Omega.omega).
              apply th2; clear th2.
              eapply NoSelfCallMeth_Impl; eauto.
           ++ apply th1; clear th1.
              eapply NoSelfCallMeth_Impl; eauto.
      * split; auto.
        split; auto.
        unfold WeakInclusion; simpl; intros.
        split; intros; auto.
  Qed.
End SimulationGen.    

Section SimulationGeneralEx.
  Variable imp spec: BaseModuleWf.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel (doUpdRegs uImp oImp) oSpec')).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
              exists oSpec',
                UpdRegs [uSpec] oSpec oSpec' /\
                simRel (doUpdRegs uImp oImp) oSpec'.

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Theorem simulationGeneralEx:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    idtac "simulationGeneralEx".
    eapply simulationGen; eauto; intros.
    - pose proof (SemAction_NoDup_u H0) as sth.
      pose proof (simRelImpGood H2) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality x; intros; auto).
      destruct (wfBaseModule imp); dest.
      rewrite <- sth3 in H6.
      rewrite <- sth2 in H6.
      rewrite sth3 in H6.
      apply NoDup_UpdRegs in H1; subst; auto.
      eapply simulationRule; eauto.
    - pose proof (SemAction_NoDup_u H0) as sth.
      pose proof (simRelImpGood H2) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality x; intros; auto).
      destruct (wfBaseModule imp); dest.
      rewrite <- sth3 in H6.
      rewrite <- sth2 in H6.
      rewrite sth3 in H6.
      apply NoDup_UpdRegs in H1; subst; auto.
      eapply simulationMeth; eauto.
  Qed.
End SimulationGeneralEx.

Section SimulationZeroA.
  Variable imp spec: BaseModuleWf.
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec ->
                                          getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec ->
                                             getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\
                                               simRel rimp rspec.

  Variable NoMeths: getMethods imp = [].
  Variable NoMethsSpec: getMethods spec = [].

  Variable simulation:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
               exists oSpec',
                 UpdRegs [uSpec] oSpec oSpec' /\
                 simRel (doUpdRegs uImp oImp) oSpec')).

  Theorem simulationZeroA:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    eapply simulationZeroAct; eauto; intros.
    pose proof (SemAction_NoDup_u H0) as sth.
    pose proof (simRelImpGood H2) as sth2.
    apply (f_equal (map fst)) in sth2.
    rewrite ?map_map in *; simpl in *.
    assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
        (intros; extensionality x; intros; auto).
    destruct (wfBaseModule imp); dest.
    rewrite <- sth3 in H6.
    rewrite <- sth2 in H6.
    rewrite sth3 in H6.
    apply NoDup_UpdRegs in H1; subst; auto.
    eapply simulation; eauto.
  Qed.
End SimulationZeroA.

Section SimulationGeneral.
  Variable imp spec: BaseModule.
  Variable NoSelfCalls: NoSelfCallBaseModule spec.
  
  Variable simRel: RegsT -> RegsT -> Prop.
  Variable simRelGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oSpec = getKindAttr (getRegisters spec).
  Variable simRelImpGood: forall oImp oSpec, simRel oImp oSpec -> getKindAttr oImp = getKindAttr (getRegisters imp).
  Variable initRel: forall rimp, Forall2 regInit rimp (getRegisters imp) ->
                                 exists rspec, Forall2 regInit rspec (getRegisters spec) /\ simRel rimp rspec.

  Variable simulationRule:
    forall oImp rImp uImp rleImp csImp aImp,
      In (rleImp, aImp) (getRules imp) ->
      SemAction oImp (aImp type) rImp uImp csImp WO ->
      forall oSpec,
        simRel oImp oSpec ->
        ((simRel (doUpdRegs uImp oImp) oSpec /\ csImp = []) \/
         (exists rleSpec aSpec,
             In (rleSpec, aSpec) (getRules spec) /\
             exists rSpec uSpec,
               SemAction oSpec (aSpec type) rSpec uSpec csImp WO /\
                 simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec))).

  Variable simulationMeth:
    forall oImp rImp uImp meth csImp sign aImp arg ret,
      In (meth, existT _ sign aImp) (getMethods imp) ->
      SemAction oImp (aImp type arg) rImp uImp csImp ret ->
      forall oSpec,
        simRel oImp oSpec ->
          exists aSpec rSpec uSpec,
            In (meth, existT _ sign aSpec) (getMethods spec) /\
            SemAction oSpec (aSpec type arg) rSpec uSpec csImp ret /\
                simRel (doUpdRegs uImp oImp) (doUpdRegs uSpec oSpec).

  Variable notMethMeth:
    forall oImp rImpl1 uImpl1 meth1 sign1 aImp1 arg1 ret1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (meth1, existT _ sign1 aImp1) (getMethods imp) ->
      SemAction oImp (aImp1 type arg1) rImpl1 uImpl1 csImp1 ret1 ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).
          
  Variable notRuleMeth:
    forall oImp rImpl1 uImpl1 rleImpl1 aImp1 csImp1
           rImpl2 uImpl2 meth2 sign2 aImp2 arg2 ret2 csImp2,
      In (rleImpl1, aImp1) (getRules imp) ->
      SemAction oImp (aImp1 type) rImpl1 uImpl1 csImp1 WO ->
      In (meth2, existT _ sign2 aImp2) (getMethods imp) ->
      SemAction oImp (aImp2 type arg2) rImpl2 uImpl2 csImp2 ret2 ->
      exists k, In k (map fst uImpl1) /\ In k (map fst uImpl2).

  Variable implWf : WfBaseModule imp.
  Variable specWf : WfBaseModule spec.

  Theorem simulationGeneral:
    TraceInclusion (Base imp) (Base spec).
  Proof.
    idtac "simulationGeneral".
    eapply simulationGeneralEx with
          (imp := {| baseModule := imp; wfBaseModule := implWf |})
          (spec := {| baseModule := spec; wfBaseModule := specWf |}) ;
      eauto; intros.
    - specialize (@simulationRule _ _ _ _ _ _ H H0 oSpec H1).
      destruct simulationRule; auto.
      dest.
      right.
      exists x, x0; repeat split; auto.
      exists x1, x2; repeat split; auto.
      exists (doUpdRegs x2 oSpec); split; auto.
      
      pose proof (SemAction_NoDup_u H3) as sth.
      destruct specWf; dest.
      pose proof (simRelGood H1) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality y; intros; auto).
      rewrite <- sth3 in H8.
      rewrite <- sth2 in H8.
      rewrite sth3 in H8.
      pose proof (SemActionUpdSub H3).
      eapply doUpdRegs_UpdRegs; eauto.
    - specialize (@simulationMeth _ _ _ _ _ _ _ _ _ H H0 oSpec H1).
      pose proof simulationMeth as sth; clear simulationMeth.
      dest.
      exists x, x0, x1; repeat split; auto.
      exists (doUpdRegs x1 oSpec); split; auto.
      pose proof (SemAction_NoDup_u H3) as sth.
      destruct specWf; dest.
      pose proof (simRelGood H1) as sth2.
      apply (f_equal (map fst)) in sth2.
      rewrite ?map_map in *; simpl in *.
      assert (sth3: forall A B, (fun x: (A * B) => fst x) = fst) by
          (intros; extensionality y; intros; auto).
      rewrite <- sth3 in H8.
      rewrite <- sth2 in H8.
      rewrite sth3 in H8.
      pose proof (SemActionUpdSub H3).
      eapply doUpdRegs_UpdRegs; eauto.
  Qed.
End SimulationGeneral.
