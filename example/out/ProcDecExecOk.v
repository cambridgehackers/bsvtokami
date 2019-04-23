Require Import Kami.All.
Require Import Kami.Tactics.
Require Import Bsvtokami.
Require Import FIFO.
Require Import ProcMemSpec ProcDecExec.
Require Import FinNotations.
Require Import BKProperties.
Require Import BKTactics.
Require Import Decoder.

Set Implicit Arguments.

(*! Specifying, implementing, and verifying a very simple processor !*)

(** You may want to take a look at the code in the following order:
 * - ProcMemSpec.v: the spec of processors and memory systems
 * - PipelinedProc.v: a 3-stage pipelined processor implementation
 * - DecExec.v: a pipeline stage that merges the first two stages,
 *   [decoder] and [executer].
 * - DecExecOk.v (you are here!): correctness of [decexec] in DecExec.v
 * - ProcMemInterm.v: an intermediate 2-stage pipelined processor 
 * - ProcMemOk.v: a complete refinement proof
 *)

Hint Unfold Empty'mod : ModuleDefs.
Hint Unfold NoMethods'mod : ModuleDefs.

(* Here we prove that merging the first two stages ([decoder] and [executer])
 * is correct by providing a refinement from [impl] to [spec]. *)
Section DecExec.

  Local Definition dataK := Bit ProcMemSpec.DataSz.
  Local Definition instK := Bit ProcMemSpec.InstrSz.

  Variables (kamidec: Decoder.Decoder)
            (kamiexec: Decoder.Executer)
            (pcInit : ConstT (Bit ProcMemSpec.PgmSz)).

  Local Definition dec: ProcMemSpec.Decoder := mkDecoder kamidec "dec".
  (* Local Definition exec: ProcMemSpec.Executer := mkExecuter kamiexec "exec". *)

  Local Definition pgm := mkRegFileFull1 NumInstrs (Bit InstrSz) "pgm".

  Local Definition e2wfifo := mkFIFO (Bit DataSz) "e2wfifo".

  Fixpoint hideMethods m meths :=
    match meths with
    | meth :: meths' => hideMethods (HideMeth m meth) meths'
    | nil => m
    end.

  Local Definition spec : Mod := 
              hideMethods (ConcatMod
  	                           (ConcatMod
  	                           (ConcatMod
                                    (NoMethods'mod (ProcDecExec.mkDecExec "spec" "pgm" "dec" kamiexec "e2wfifo"))
				     (RegFile'mod pgm))
				     (ProcMemSpec.Decoder'mod dec))

				     (FIFO'mod e2wfifo))
             ("e2wfifo-first" :: "e2wfifo-deq" :: "e2wfifo-clear" :: "e2wfifo-enq"
             :: "pgm-sub" :: "dec-getOp" :: "dec-getArithOp" :: "dec-getSrc1" :: "dec-getSrc2" :: "dec-getDst" :: "dec-getAddr" :: nil).


  Local Definition impl : Mod := 
             hideMethods (ConcatMod
  	                           (ConcatMod
  	                           (ConcatMod
                                    (NoMethods'mod (ProcDecExec.mkDecExecSep "impl" "pgm" "dec" kamiexec "e2wfifo"))
				     (RegFile'mod pgm))
				    (ProcMemSpec.Decoder'mod dec))
                                    (FIFO'mod e2wfifo))
             ("e2wfifo-first" :: "e2wfifo-deq" :: "e2wfifo-clear" :: "e2wfifo-enq"
             :: "pgm-sub" :: "dec-getOp" :: "dec-getArithOp" :: "dec-getSrc1" :: "dec-getSrc2" :: "dec-getDst" :: "dec-getAddr" :: nil).

  (* What would be good invariants to prove the correctness of stage merging?
   * For two given stages, we usually need to provide relations among states in
   * the two stages and elements in the fifo between them.
   *
   * Here we describe two invariants: the first one [decexec_pc_inv] states a
   * relation between the [pc] value and the fifo element, and the second one
   * [decexec_d2e_inv] states that the fifo element is valid with respect to the
   * current instruction. *)
  Definition decexec_pc_inv
             (impl_pcv: fullType type (SyntaxKind (Bit PgmSz)))
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2e_pcv:      word PgmSz) :=
             (d2efullv = true ) -> (impl_pcv = d2e_pcv ^+ $1 ).
  
  Definition decexec_d2e_inv
             (pgmv: fullType type (SyntaxKind (Array NumInstrs (Bit InstrSz))))
             (impl_pcv:         word PgmSz)
             (d2e_pcv:      word PgmSz)
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2e_addrv:    word AddrSz)
             (d2e_arithopv: fullType type (SyntaxKind OpArithK))
             (d2e_opv:      fullType type (SyntaxKind OpK))
             (d2e_pcv:      word PgmSz)
             (d2e_dstv:     word RegFileSz)
             (d2e_src1v:    word RegFileSz)
             (d2e_src2v:    word RegFileSz) :=
    (d2efullv = true) -> (
    let inst := evalExpr (ReadArray (Var type (SyntaxKind _) pgmv) (Var type (SyntaxKind (Bit PgmSz)) d2e_pcv )) in
    d2e_opv = evalExpr (getOp kamidec _ inst) /\
    d2e_arithopv = evalExpr (getArithOp kamidec _ inst) /\
    d2e_src1v = evalExpr (getSrc1 kamidec _ inst) /\
    d2e_src2v = evalExpr (getSrc2 kamidec _ inst) /\
    d2e_dstv = evalExpr (getDst kamidec _ inst) /\
    d2e_addrv = evalExpr (getAddr kamidec _ inst) /\
    impl_pcv = (wzero PgmSz ^+ d2e_pcv ^+ $1)
    ).


  (* Make sure to register all invariant-related definitions in the [InvDefs]
   * hint database, in order for Kami invariant-solving tactics to unfold them
   * automatically. *)
  Hint Unfold decexec_pc_inv decexec_d2e_inv: InvDefs.

End DecExec.

Hint Unfold dec : ModuleDefs.
Hint Unfold pgm : ModuleDefs.
Hint Unfold e2wfifo: ModuleDefs.
Hint Unfold spec: ModuleDefs.
Hint Unfold impl: ModuleDefs.

Local Ltac constructor_simpl :=
  econstructor; eauto; simpl; unfold not; intros.

Local Ltac bk_discharge_wf :=
  repeat match goal with
         | |- @WfMod _ => constructor_simpl
         | |- @WfConcat _ _ => constructor_simpl
         | |- _ /\ _ => constructor_simpl
         | |- @WfConcatActionT _ _ _ => constructor_simpl
         | |- @WfBaseModule _ => idtac "WBM"; constructor_simpl
         | |- @WfActionT _ _ (convertLetExprSyntax_ActionT ?e) => apply WfLetExprSyntax
         | |- @WfActionT _ _ _ => constructor_simpl
         | |- NoDup _ => constructor_simpl
         | H: _ \/ _ |- _ => destruct H; subst; simpl
         (* | |- DisjKey _ _ => discharge_DisjKey *)
         end;
  discharge_DisjKey.

Section ImplOk.
  Variable decoder: Decoder.Decoder.
  Variable executer: Decoder.Executer.
  Check dec.
  Theorem dec_wf:
    WfMod (ProcMemSpec.Decoder'mod (dec decoder)).
  Proof.
    repeat autounfold with ModuleDefs.
    bk_discharge_wf.
  Qed.

  Theorem pgm_wf:
    WfMod (RegFile'mod pgm).
  Proof.
    repeat autounfold with ModuleDefs.
    bk_discharge_wf.
  Qed.
  Theorem e2wfifo_wf:
    WfMod (FIFO'mod e2wfifo).
  Proof.
    repeat autounfold with ModuleDefs.
    bk_discharge_wf.
  Qed.
  Theorem spec_wfmod:
     WfMod (spec decoder executer).
  Proof.
    repeat autounfold with ModuleDefs.
    discharge_wf.
  Qed.


  Definition specMod := (spec decoder executer).
  Hint Unfold specMod : ModuleDefs.
  Definition implMod := (impl decoder executer).
  Hint Unfold implMod : ModuleDefs.

  Definition specInl := flatten_inline_remove specMod.
  Definition implInl := flatten_inline_remove implMod.

  Hint Unfold specInl : ModuleDefs.
  Hint Unfold implInl : ModuleDefs.


Local Ltac repeat_autounfold_moduledefs := 
  repeat autounfold with ModuleDefs ;
  idtac "unfolded moduledefs".

Ltac unfold_flatten_inline_remove :=
  unfold hideMethods ; unfold flatten_inline_remove ;
  unfold inlineAll_All_mod ; simpl ;
  unfold getAllRegisters ; simpl ;
  unfold inlineAll_All ; simpl ;
  unfold inlineAll_Meths ; simpl ;
  idtac "unfolding inlineSingle_Meths_pos" ;
  try (unfold inlineSingle_Meths_pos at 11 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 10 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 9 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 8 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 7 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 6 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 5 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 4 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 3 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 2 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 1 ; simpl) ;
  idtac "unfolding inlineSingle_Meths_pos" ;
  try (unfold inlineSingle_Meths_pos at 11 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 10 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 9 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 8 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 7 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 6 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 5 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 4 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 3 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 2 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 1 ; simpl) ;
  idtac "unfolding inlineSingle_Meths_pos" ;
  try (unfold inlineSingle_Meths_pos at 11 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 10 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 9 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 8 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 7 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 6 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 5 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 4 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 3 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 2 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 1 ; simpl) ;
  idtac "unfolding inlineSingle_Meths_pos" ;
  try (unfold inlineSingle_Meths_pos at 11 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 10 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 9 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 8 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 7 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 6 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 5 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 4 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 3 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 2 ; simpl) ;
  try (unfold inlineSingle_Meths_pos at 1 ; simpl) ;
  idtac "unfolding inlineAll_Rules" ;
  unfold inlineAll_Rules ; unfold Datatypes.length ; unfold range ; simpl ;
  unfold inlineSingle_Rules_pos ; simpl ;
  unfold removeHides ;
  unfold getRegisters ; unfold getRules ; unfold getMethods ;
  unfold in_dec ; unfold getBool ; unfold negb ; unfold filter ; simpl ;
  idtac "flatten_inline_remove".

Ltac discharge_flatten_inline_remove :=
  time repeat_autounfold_moduledefs ;
  time unfold_flatten_inline_remove.  

(*
Theorem implInlWf:
  WfBaseModule implInl.
Proof.
  idtac "implInlWf".
  discharge_flatten_inline_remove.
  idtac "discharging wf"
  time discharge_wf.
Qed.
 
Theorem specInlWf:
  WfBaseModule specInl.
Proof.
  idtac "specInlWf".
  discharge_flatten_inline_remove.
  idtac "discharging wf"
  time discharge_wf.
Qed.

*)

Record mySimRel (dec : Decoder) (iregs sregs: RegsT): Prop :=
 {
   pgmv: (Fin.t NumInstrs -> word DataSz) ;

   impl_d2e_validv: bool ;
   impl_pcv: word PgmSz ;
   impl_e2w_validv: fullType type (SyntaxKind (Bit 1)) ;
   impl_e2w_valv: fullType type (SyntaxKind (Bit DataSz)) ;
   impl_rf_v: fullType type (SyntaxKind (Array NumRegs (Bit DataSz))) ;

   spec_pcv: word PgmSz ;
   spec_e2w_validv: fullType type (SyntaxKind (Bit 1)) ;
   spec_e2w_valv: fullType type (SyntaxKind (Bit DataSz)) ;
   spec_rf_v: (Fin.t NumRegs -> word DataSz) ;

   impl_d2e_addrv    : word AddrSz ;
   impl_d2e_arithopv : fullType type (SyntaxKind OpArithK) ;
   impl_d2e_opv      : fullType type (SyntaxKind OpK) ;
   impl_d2e_pcv      : word PgmSz ;
   impl_d2e_dstv     : word RegFileSz ;
   impl_d2e_src1v    : word RegFileSz ;
   impl_d2e_src2v    : word RegFileSz ;

   Hiregs: iregs =
   ("impl-pc", existT _ (SyntaxKind (Bit PgmSz)) impl_pcv)
   :: ("impl-d2e_valid", existT _ (SyntaxKind Bool) impl_d2e_validv)
   :: ("impl-d2e_pc", existT _ (SyntaxKind (Bit PgmSz)) impl_d2e_pcv)
   :: ("impl-d2e_op", existT _ (SyntaxKind OpK) impl_d2e_opv)
   :: ("impl-d2e_arithOp", existT _ (SyntaxKind OpArithK) impl_d2e_arithopv)
   :: ("impl-d2e_src1", existT _ (SyntaxKind (Bit RegFileSz)) impl_d2e_src1v)
   :: ("impl-d2e_src2", existT _ (SyntaxKind (Bit RegFileSz)) impl_d2e_src2v)
   :: ("impl-d2e_dst", existT _ (SyntaxKind (Bit RegFileSz)) impl_d2e_dstv)
   :: ("impl-rf", existT _ (SyntaxKind (Array NumRegs (Bit DataSz))) impl_rf_v)
   :: ("pgm-rfreg", existT _ (SyntaxKind (Array NumInstrs (Bit InstrSz))) pgmv)
   :: ("e2wfifo-valid", existT (fullType type) (SyntaxKind (Bit 1)) impl_e2w_validv)
   :: ("e2wfifo-v", existT (fullType type) (SyntaxKind (Bit DataSz)) impl_e2w_valv)
   :: nil ;

   Hsregs: sregs =
    ("spec-pc", existT (fullType type) (SyntaxKind (Bit PgmSz)) spec_pcv)
    :: ("spec-rf", existT (fullType type) (SyntaxKind (Array NumRegs (Bit DataSz))) spec_rf_v)
    :: ("pgm-rfreg", existT (fullType type) (SyntaxKind (Array NumInstrs (Bit InstrSz))) pgmv)
    :: ("e2wfifo-valid", existT (fullType type) (SyntaxKind (Bit 1)) spec_e2w_validv)
    :: ("e2wfifo-v", existT (fullType type) (SyntaxKind (Bit DataSz)) spec_e2w_valv)
    :: nil ;

   Hpcinv: (impl_d2e_validv = true ) -> (impl_pcv = impl_d2e_pcv ^+ $1 /\ spec_pcv = impl_d2e_pcv) ;
   Hpcinv_decode: (impl_d2e_validv = false ) -> (impl_pcv = spec_pcv) ;
   Hdeinv: decexec_d2e_inv dec pgmv impl_pcv
               impl_d2e_pcv
               impl_d2e_validv
               impl_d2e_addrv
               impl_d2e_arithopv
               impl_d2e_opv
               impl_d2e_pcv
               impl_d2e_dstv 
               impl_d2e_src1v
               impl_d2e_src2v ;

   He2w_valid: impl_e2w_validv = spec_e2w_validv ;
   He2w_val:   impl_e2w_validv = (natToWord 1 1) ->  impl_e2w_valv = spec_e2w_valv ;

 }.

Ltac unfold_mySimRel :=
  match goal with
   | [ |- ?goal ] => idtac "mySimRel" ; simple refine goal
   end.

Ltac bk_discharge_simulationZero mySimRel :=
  apply simulationZeroAction with (simRel := mySimRel) ; auto; simpl; intros;
  (repeat match goal with
          | H: _ \/ _ |- _ => destruct H
          | H: False |- _ => exfalso; apply H
          | H: (?a, ?b) = (?c, ?d) |- _ =>
            let H2 := fresh in
            inversion H;
            pose proof (f_equal snd H) as H2 ;
            simpl in H2; subst; clear H; EqDep_subst
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
          | H: SemAction _ _ _ _ _ _ |- _ =>
            apply inversionSemAction in H; dest; subst
          | H: if ?P then _ else _ |- _ => case_eq P; let i := fresh in intros i; rewrite ?i in *; dest
          | H: Forall2 _ _ _ |- _ => inv H
          | H: ?a = ?a |- _ => clear H
          | H: match convertLetExprSyntax_ActionT ?P with
               | _ => _
               end |- _ =>
            case_eq P; intros;
            match goal with
            | H': P = _ |- _ => rewrite ?H' in *; simpl in *; try discriminate
            end
          end) ; dest; simpl in *; repeat subst; simpl in *.

Ltac andb_true_intro_split := apply andb_true_intro; split.

Lemma findStr A B (dec: forall a1 a2, {a1 = a2} + {a1 <> a2}):
  forall (ls: list (A * B)),
  forall x, In x ls <->
            In x (filter (fun t => getBool (dec (fst x) (fst t))) ls).
Proof.
  induction ls; simpl; split; auto; intros.
  - destruct H; [subst|]; auto.
    + destruct (dec (fst x) (fst x)) ; simpl in *; tauto.
    + apply IHls in H.
      destruct (dec (fst x) (fst a)) ; simpl in *; auto.
  - destruct (dec (fst x) (fst a)) ; simpl in *.
    + destruct H; auto.
      apply IHls in H; auto.
    + eapply IHls in H; eauto.
Qed.

Ltac foo :=
    subst;
    repeat
      (match goal with
       | H:DisjKey _ _
         |- _ =>
         apply DisjKeyWeak_same in H;
           [ unfold DisjKeyWeak in H; simpl in H | apply string_dec ]
       | H: In ?x ?ls |- _ =>
         apply (findStr string_dec) in H; simpl in H; destruct H; [|exfalso; auto]
       | H:False |- _ => exfalso; apply H
       | H:(?A, ?B) = (?P, ?Q)
         |- _ =>
         let H1 := fresh in
         let H2 := fresh in
         pose proof (f_equal fst H) as H1; pose proof (f_equal snd H) as H2; simpl in H1, H2;
           clear H
       | H:?A = ?A |- _ => clear H
       | H:(?a ++ ?b)%string = (?a ++ ?c)%string |- _ => rewrite append_remove_prefix in H; subst
       | H:(?a ++ ?b)%string = (?c ++ ?b)%string |- _ => rewrite append_remove_suffix in H; subst
       | H:existT ?a ?b ?c1 = existT ?a ?b ?c2
         |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H
       | H:?A = ?B |- _ => discriminate
       | H: ?x && ?y = true |- _ => rewrite andb_true_iff in H
       | H: negb ?x = true |- _ => apply negb_true_iff in H
       | H: negb ?x = false |- _ => apply negb_false_iff in H
       | H: ?x /\ ?y |- _ => destruct H
       | H:SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _
         |- _ => apply convertLetExprSyntax_ActionT_full in H; dest
       | |- _ -> _ => intro
       | |- ?a = ?a => reflexivity
       end; subst).

Ltac discharge_whatever :=
  repeat (match goal with
          | H: _ |- Forall2 ?p ?l1 ?l2 => apply Forall2_cons; simpl
          | H: _ |- Forall2 ?p nil nil => apply Forall2_nil
          | H: _ |- ?a /\ ?b => split
          | H: _ |- _ :: _ = _ :: _ => repeat f_equal
          | H: _ |- ?a = ?a => reflexivity
          | H: _ |- exists _, _ => exists eq_refl
          end).

Ltac discharge_simulationGeneralWf mySimRel :=
  match goal with
  | |- (TraceInclusion ?wfm1 ?wfm2) =>
       apply simulationGeneral with (simRel := mySimRel)
               (imp := (Syntax.module wfm1)) (spec := (Syntax.module wfm2))
  end.

Ltac bk_discharge_simulationGeneral mySimRel :=
  apply BKProperties.simulationGeneral with (simRel := mySimRel) ; auto; simpl; intros;
  try match goal with
      | H: mySimRel _ _ |- _ => inv H
      end;
  clean_hyp; auto; clean_hyp.

Theorem impl_ok:
    TraceInclusion implInl specInl 
(*
                   (getModWf {| baseModule := implInl ; wfBaseModule := ltac:(apply implInlWf) |})
                   (getModWf {| baseModule := specInl ; wfBaseModule := ltac:(apply specInlWf) |})
*).
  Proof.
  idtac "impl_ok".
  discharge_flatten_inline_remove.
  idtac "apply simulationGeneral".
  time bk_discharge_simulationGeneral (mySimRel decoder).
  + reflexivity.

  + (* decode rule *)
    left. split.
    * (* simRel oImp' oSpec *)
     evar (impl_d2e_validv0 : bool).
     evar (impl_pcv0 : word PgmSz).
     econstructor 1 with (impl_d2e_validv := impl_d2e_validv0) (pgmv := x5) (impl_pcv := impl_pcv0) (spec_pcv := x).
     ** repeat (f_equal; foo). instantiate (impl_d2e_validv0 := true). unfold impl_d2e_validv0.
        rewrite wzero_wplus. unfold impl_pcv0; reflexivity. unfold impl_d2e_validv0; reflexivity.
     ** repeat f_equal. admit.
     ** foo. unfold impl_pcv0; split; reflexivity; reflexivity.
     ** unfold impl_d2e_validv0. foo.
     ** econstructor. simpl.
      *** reflexivity.
      *** simpl. repeat split. unfold impl_pcv0. rewrite wzero_wplus; reflexivity.
     ** reflexivity.
     ** admit.
    * reflexivity.

  + (* arith rule *)
    right. exists "spec-decexecArith". eexists. split.
    * left. trivial.
    * (* reads spec *) eexists. (* updates spec *) eexists. split.
     ** discharge_SemAction.
        destruct Hdeinv. admit. simpl in H.
          destruct Hpcinv. admit. rewrite H2. (* rewrite <- H. simpl in H. apply H.
      *** rewrite negb_true_iff. reflexivity. *) admit.

     ** 
evar (impl_d2e_validv0 : bool).
econstructor 1 with (impl_d2e_validv := impl_d2e_validv0).
     *** repeat f_equal. unfold impl_d2e_validv0. trivial.
     *** simpl. repeat f_equal.
     *** intro. inv H.
     *** unfold impl_d2e_validv0. intro. foo. destruct Hpcinv.
         **** reflexivity.
         **** rewrite H1. rewrite H0. rewrite wzero_wplus. reflexivity.
     *** econstructor. foo. foo.
     *** reflexivity.
     *** intro; reflexivity.
     *** intro. destruct Hdeinv. foo.
      **** foo. simpl. destruct Hpcinv. reflexivity. rewrite H1. reflexivity.

  + discharge_wf.
  + discharge_wf.

Qed.
End ImplOk.
