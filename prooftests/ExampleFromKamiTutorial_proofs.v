Require Import Bool String List Arith.
Require Import Kami.All.
Require Import BK.Bsvtokami.
Require Import BK.ExampleFromKamiTutorial.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Ltac discharge_disjKey :=
   match goal with
   | |- DisjKey ?P ?Q => rewrite DisjKeyWeak_same by apply string_dec;
                         let k := fresh in
                         let H1 := fresh in
                         let H2 := fresh in
                         unfold DisjKeyWeak; simpl; intros k H1 H2;
                         repeat destruct H1; repeat destruct H2; subst; auto; try discriminate
   end.

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

Definition hiddenMethods := ( ("c0" -- "send")%string :: nil).
Definition producerModules := (ConcatMod (createHideMod (ConcatMod (Producer'mod producer) (Consumer'mod consumer)) hiddenMethods)
 (ExtCall'mod extcall)).

Hint Unfold producerModules : ModuleDefs.

Definition producerConsumer := mkProduceConsume "p0" extcall.
Hint Unfold producerConsumer : ModuleDefs.
Definition producerConsumerModules := ConcatMod (Foo'mod producerConsumer) (ExtCall'mod extcall).
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
  TraceInclusion producerConsumerModules producerConsumerModules.
Proof.
  apply TraceInclusion_refl.
Qed.

Check (head (snd (separateBaseMod producerModules))).

Theorem wf_consumer ty:
  WfMod ty (Consumer'mod consumer).
Proof.
  repeat autounfold with ModuleDefs.
  repeat econstructor; eauto.
  intuition. (* no rules *)
  unfold getMethods. simpl.
    intro.
    intro.
    intuition.
    subst.
    repeat econstructor.
Qed.

Theorem wf_extcall ty:
  WfMod ty (ExtCall'mod extcall).
Proof.
    repeat autounfold with ModuleDefs.
    repeat econstructor; eauto.
    intuition.
    unfold getMethods.
    simpl. intro. intro. intuition. subst. repeat econstructor.
Qed.

Definition prodrule := (("p0" -- "produce_rule",
            fun ty : Kind -> Type =>
            (Call data_v : Bit 32 <- (("p0" -- "data") -- "_read") () ;
             Call _ : Void <- ("c0" -- "send") ( ( #data_v ) : Bit 32 ) ;
             LET new_data_v : Bit 32 <-  ( (# data_v) + ($$(natToWord 32 1)) )%kami_expr ;
             Call _ : Void <- (("p0" -- "data") -- "_write") ( (# new_data_v) : Bit 32) ;
             Retv)%kami_action)%kami).
Definition prodcore : BaseModule := (BaseMod nil
            ((("p0" -- "produce_rule",
            fun ty : Kind -> Type =>
            (Call data_v : Bit 32 <- (("p0" -- "data") -- "_read") () ;
             Call _ : Void <- ("c0" -- "send") ( ( #data_v ) : Bit 32 ) ;
             LET new_data_v : Bit 32 <-  ( (# data_v) + ($$(natToWord 32 1)) )%kami_expr ;
             Call _ : Void <- (("p0" -- "data") -- "_write") ( (# new_data_v) : Bit 32) ;
             Retv)%kami_action)%kami) :: nil) nil)%kami.

Theorem wf_prodcore ty:
  WfMod ty (Base
     (BaseMod nil
        (("p0" -- "produce_rule",
         fun ty : Kind -> Type =>
         (Call data_v : Bit 32 <- (("p0" -- "data") -- "_read") () ;
          Call _ : Void <- ("c0" -- "send") (Var ty (SyntaxKind (fst (Bit 32, Void))) data_v : Bit 32) ;
          Call _ : Void <- (("p0" -- "data") -- "_write") (Var ty (SyntaxKind (snd (Void, Bit 32))) data_v +
                                                           Const ty ($1)%word : Bit 32) ;
          Retv)%kami_action) :: nil)
        nil)).
Proof.
  repeat econstructor; eauto. 
  + unfold getRules. simpl. intro. intro. intuition. rewrite <- H0.
    repeat econstructor; eauto.
  + unfold getMethods. simpl. intro. intro. intuition.
Qed.

Theorem wf_prodconsumercore ty:
  WfMod ty (Base
              (BaseMod nil
                       (("p0" -- "produce_rule",
                         fun ty : Kind -> Type =>
                           (Call data_v : Bit 32 <- (("p0" -- "data") -- "_read") () ;
                              Call _ : Void <- ("e0" -- "extCall") (Var ty (SyntaxKind (fst (Bit 32, Void))) data_v : 
                                                                      Bit 32) ;
                              Call _ : Void <- (("p0" -- "data") -- "_write")
                                            (Var ty (SyntaxKind (snd (Void, Bit 32))) data_v + Const ty ($1)%word : 
                                               Bit 32) ; Retv)%kami_action) :: nil) nil)).
Proof.
  repeat econstructor; eauto. 
  + unfold getRules. simpl. intro. intro. intuition. rewrite <- H0.
    repeat econstructor; eauto.
  + unfold getMethods. simpl. intro. intro. intuition.
Qed.

Theorem something:
  ~ ("p0-data-_write" = "p0-data-_read" \/ False).
Proof.
 intro sth. inv sth.
 + inv H.
 + inv H.
Qed.

Theorem wf_bar ty:
  WfMod ty
    (Base
       (BaseMod ((("p0" -- "data") -- "reg", existT optConstFullT (SyntaxKind (Bit 32)) (Some (makeConst $0))) :: nil) nil
          ((("p0" -- "data") -- "_read", existT MethodT (Void, Bit 32) (fun (ty : Kind -> Type) (_ : ty Void) => (Read v : Bit 32 <- ("p0" -- "data") -- "reg"; Ret Var ty (SyntaxKind (Bit 32)) v)%kami_action))
           :: (("p0" -- "data") -- "_write", existT MethodT (Bit 32, Void) (fun (ty : Kind -> Type) (v : ty (Bit 32)) => (Write ("p0" -- "data") -- "reg" : Bit 32 <- Var ty (SyntaxKind (Bit 32)) v; Retv)%kami_action))
           :: nil))).
Proof.
  repeat econstructor; eauto.
  + intro. unfold getRules. unfold In. intuition.
  + unfold getMethods. simpl. intro. intuition.
    - subst. simpl. repeat econstructor; eauto.
    - subst. simpl. repeat econstructor; eauto.
  + simpl. intuition. inv H0.
Qed.

Theorem wf_foo ty:
  WfMod ty
  (Base
     (BaseMod
        ((("p0" -- "data") -- "reg",
         existT optConstFullT (SyntaxKind (Bit 32)) (Some (makeConst $0))) :: nil) nil
        ((("p0" -- "data") -- "_read",
         existT MethodT (Void, Bit 32)
           (fun (ty : Kind -> Type) (_ : ty Void) =>
            (Read v : Bit 32 <- ("p0" -- "data") -- "reg";
             Ret Var ty (SyntaxKind (Bit 32)) v)%kami_action))
         :: (("p0" -- "data") -- "_write",
            existT MethodT (Bit 32, Void)
              (fun (ty : Kind -> Type) (v : ty (Bit 32)) =>
               (Write ("p0" -- "data") -- "reg" : Bit 32 <-
                Var ty (SyntaxKind (Bit 32)) v; Retv)%kami_action)) :: nil))).
Proof.
  repeat econstructor; eauto.
  + intuition.
  + unfold getMethods. simpl. intro. intuition.
    - subst. simpl. repeat econstructor; eauto.
    - subst. simpl. repeat econstructor; eauto.
  + simpl. intro sth. inv sth.
    - inv H.
    - inv H.
Qed.

Theorem wf_reg ty:
  WfMod ty (Reg'mod (mkReg "p0-data" (ConstBit (natToWord 32 0)))).
Proof.
  repeat autounfold with ModuleDefs.
  repeat econstructor; eauto.
  + unfold getRules. simpl. tauto.
  + unfold getMethods. simpl.
    intro. intro.
    intuition.
    - subst. repeat econstructor; eauto.
    - subst. repeat econstructor; eauto.
  + simpl. intro sth. inv sth. * inv H. * inv H.
Qed.

Theorem wf_mkreg ty:
  WfMod ty (Base
              (BaseMod ((("p0" -- "data") -- "reg", existT optConstFullT (SyntaxKind (Bit 32)) (Some (makeConst $0))) :: nil) nil
                       ((("p0" -- "data") -- "_read", existT MethodT (Void, Bit 32) (fun (ty : Kind -> Type) (_ : ty Void) => (Read v : Bit 32 <- ("p0" -- "data") -- "reg"; Ret Var ty (SyntaxKind (Bit 32)) v)%kami_action))
                          :: (("p0" -- "data") -- "_write", existT MethodT (Bit 32, Void) (fun (ty : Kind -> Type) (v : ty (Bit 32)) => (Write ("p0" -- "data") -- "reg" : Bit 32 <- Var ty (SyntaxKind (Bit 32)) v; Retv)%kami_action))
                          :: nil))).
Proof.
  repeat econstructor; eauto.
  + unfold getRules. simpl. tauto.
  + unfold getMethods. simpl.
    intro. intro.
    intuition.
    - subst. repeat econstructor; eauto.
    - subst. repeat econstructor; eauto.
  + simpl. intro sth. inv sth. * inv H. * inv H.
Qed.
  

Ltac discharge_disj_registers:=
   match goal with
   | |- DisjKey (getAllRegisters ?M1)  (getAllRegisters ?M2) => 
        unfold getAllRegisters; unfold getRegisters; unfold app; discharge_disjKey
  end.
Ltac discharge_disj_rules:=
   match goal with
   | |- DisjKey (getAllRules ?M1)  (getAllRules ?M2) => 
        unfold getAllRules; unfold getRules; unfold app; discharge_disjKey
  end.
Ltac discharge_disj_methods:=
   match goal with
   | |- DisjKey (getAllMethods ?M1)  (getAllMethods ?M2) => 
        unfold getAllMethods; unfold getMethods; unfold app; discharge_disjKey
  end.

Theorem wf_producerconsumer ty:
  WfMod ty producerConsumerModules.
Proof.
    unfold producerConsumerModules.
    repeat autounfold with ModuleDefs.
    apply ConcatModWf.
    + unfold getAllRegisters. unfold getRegisters. unfold app. discharge_disjKey.
    + unfold getAllRules. unfold getRules. discharge_disjKey.
    + unfold getAllMethods. unfold getMethods. discharge_disjKey.
    + apply ConcatModWf.
      * discharge_disj_registers.
      * discharge_disj_rules.
      * discharge_disj_methods.
      * apply wf_prodconsumercore.
      * apply wf_mkreg.
      * repeat econstructor; eauto.
        - apply WfConcat_noHide. unfold getHidden. reflexivity.
        - unfold getAllMethods. unfold getMethods. intuition.
          * apply WfConcat_noHide. unfold getHidden. reflexivity.
  + repeat econstructor; eauto. intuition.
    * intro. unfold getMethods. unfold In. repeat econstructor; eauto. intro. intuition. subst. repeat econstructor ; eauto.
      + apply WfConcat_noHide. unfold getHidden. reflexivity.
      + apply WfConcat_noHide. unfold getHidden. reflexivity.
Qed.

Theorem producer_consumer_refinement2:
  TraceInclusion producerConsumerModules (flatten producerConsumerModules).
Proof.
  repeat autounfold with ModuleDefs.
  Search (TraceInclusion _ _).
  apply TraceInclusion_flatten_r.
  apply wf_producerconsumer.
Qed.

Check DisjKey.
Compute DisjKey.

Theorem wf_producer:
  WfMod producerModules .
Proof.
  repeat autounfold with ModuleDefs.
  Search (WfMod (ConcatMod _ _ )).
  apply ConcatModWf.
  + unfold DisjKey. simpl. intuition.
  + unfold DisjKey. simpl. intuition.
  + unfold getAllMethods. unfold getMethods. unfold app. discharge_disjKey.
  + apply ConcatModWf. 
    * unfold getAllRegisters. unfold getRegisters. unfold app. discharge_disjKey.
    * unfold getAllRules. unfold getRules. discharge_disjKey.
    * unfold getAllMethods. unfold getMethods. unfold app. discharge_disjKey.
    * apply ConcatModWf.
      - unfold getAllRegisters. unfold getRegisters. discharge_disjKey.
      - unfold getAllRules. unfold getRules. unfold app. discharge_disjKey.
      - unfold getAllMethods. unfold getMethods. unfold app. discharge_disjKey.
      - apply wf_prodcore.
      - apply wf_foo. 
      - apply WfConcat_noHide. unfold getHidden. reflexivity.
      - apply WfConcat_noHide. unfold getHidden. reflexivity.
    * apply wf_consumer.
    * apply WfConcat_noHide. unfold getHidden. reflexivity.
    * apply WfConcat_noHide. unfold getHidden. reflexivity.
  + repeat econstructor; eauto. unfold getRules. intro. intuition.
 unfold getMethods. intro. unfold In. intuition. subst. repeat econstructor; eauto.
  + apply WfConcat_noHide. unfold getHidden. reflexivity.
  + apply WfConcat_noHide. unfold getHidden. unfold app. reflexivity.
Qed.

Lemma Trace_createHideMod l m m':
    TraceInclusion m m' ->
    TraceInclusion (createHideMod m l) (createHideMod m' l).
  Proof.
    induction l; simpl in *; auto.
    intros.
    apply TraceInclusion_TraceInclusion' in H.
    apply TraceInclusion'_TraceInclusion.
    apply TraceInclusion_createHide.
    apply TraceInclusion_TraceInclusion'; apply TraceInclusion'_TraceInclusion in H; auto.
  Qed.

Theorem producer_consumer_refinement3:
  TraceInclusion (flatten producerConsumerModules) (flatten producerModules).
Proof.
  repeat autounfold with ModuleDefs.
  + unfold getAllMethods. unfold getMethods. unfold getHidden. unfold app. unfold map. unfold fst. intro. apply iff_refl.
  + intro. apply iff_refl.
Admitted.

Theorem producer_consumer_refinement4:
  TraceInclusion producerConsumerModules producerModules.
Proof.
  repeat autounfold with ModuleDefs.
  unfold hiddenMethods.
  unfold createHideMod.
  apply ModularSubstition.


Qed.
