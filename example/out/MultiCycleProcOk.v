Require Import Kami.All.
Require Import Kami.Tactics.
Require Import Bsvtokami.
Require Import FIFO.
Require Import ProcMemSpec PipelinedProc MultiCycleProc ProcDecExec.
Require Import FinNotations.
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

(* Here we prove that merging the first two stages ([decoder] and [executer])
 * is correct by providing a refinement from [decexecSep] to [decexec]. *)
Section DecExec.

  Local Definition dataK := Bit ProcMemSpec.DataSz.
  Local Definition instK := Bit ProcMemSpec.InstrSz.

  Variables (kamidec: Decoder.Decoder)
            (kamiexec: Decoder.Executer)
(spec impl: BaseModule)
            (pcInit : ConstT (Bit ProcMemSpec.PgmSz)).

  Local Definition multicycle : Mod := (Empty'mod (MultiCycleProc.mkMultiCycleProc "spec" kamidec kamiexec)).
  Hint Unfold multicycle: ModuleDefs.

  Local Definition dec: ProcMemSpec.Decoder := mkDecoder kamidec "dec".
  Local Definition exec: ProcMemSpec.Executer := mkExecuter kamiexec "exec".

  Local Definition decexecSep : Mod := (Empty'mod (ProcDecExec.mkDecExecSep  "impl" kamidec kamiexec)).
  Hint Unfold decexecSep: ModuleDefs.

  Local Definition decexecSepInl := (flatten_inline_remove decexecSep).

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

Section DecExecSepOk.
  Variable dec: Decoder.Decoder.

  Record mySimRel (iregs sregs: RegsT): Prop :=
   {
     pgmv: (Fin.t NumInstrs -> word DataSz) ;

     impl_d2efifo_validv: bool ;
     impl_pcv: word PgmSz ;
     impl_e2wfifo_validv: bool ;
     impl_e2wfifo_idxv: fullType type (SyntaxKind (Bit RegFileSz)) ;
     impl_e2wfifo_valv: fullType type (SyntaxKind (Bit DataSz)) ;
     impl_rf_v: fullType type (SyntaxKind (Array 32 (Bit DataSz))) ;

     spec_pcv: word PgmSz ;
     spec_decoder_pcv : word PgmSz ;
     spec_decoder_addrv : word AddrSz ;
     spec_decoder_arithOpv : fullType type (SyntaxKind OpArithK) ;
     spec_decoder_opv : fullType type (SyntaxKind OpK) ;
     spec_decoder_dstv : fullType type (SyntaxKind (Bit (Nat.log2_up 32))) ; 
     spec_decoder_src1v : fullType type (SyntaxKind (Bit (Nat.log2_up 32))) ;
     spec_decoder_src2v : fullType type (SyntaxKind (Bit (Nat.log2_up 32))) ;
     spec_exec_dstv : fullType type (SyntaxKind (Bit (Nat.log2_up 32))) ;
     spec_exec_valv : word DataSz ;
     spec_refproc_statev : word 2 ;
     spec_rf_v: (Fin.t 32 -> word DataSz) ;

     impl_d2efifo_addrv    : word AddrSz ;
     impl_d2efifo_arithopv : fullType type (SyntaxKind OpArithK) ;
     impl_d2efifo_opv      : fullType type (SyntaxKind OpK) ;
     impl_d2efifo_pcv      : word PgmSz ;
     impl_d2efifo_dstv     : word RegFileSz ;
     impl_d2efifo_src1v    : word RegFileSz ;
     impl_d2efifo_src2v    : word RegFileSz ;

     Hiregs: iregs =
     ("impl-pc", existT _ (SyntaxKind (Bit PgmSz)) impl_pcv)
     :: ("impl-d2eFifo_valid", existT _ (SyntaxKind Bool) impl_d2efifo_validv)
     :: ("impl-d2eFifo_addr", existT _ (SyntaxKind (Bit AddrSz)) impl_d2efifo_addrv)
     :: ("impl-d2eFifo_arithOp", existT _ (SyntaxKind OpArithK) impl_d2efifo_arithopv)
     :: ("impl-d2eFifo_op", existT _ (SyntaxKind OpK) impl_d2efifo_opv)
     :: ("impl-d2eFifo_pc", existT _ (SyntaxKind (Bit PgmSz)) impl_d2efifo_pcv)
     :: ("impl-d2eFifo_dst", existT _ (SyntaxKind (Bit RegFileSz)) impl_d2efifo_dstv)
     :: ("impl-d2eFifo_src1", existT _ (SyntaxKind (Bit RegFileSz)) impl_d2efifo_src1v)
     :: ("impl-d2eFifo_src2", existT _ (SyntaxKind (Bit RegFileSz)) impl_d2efifo_src2v)
     :: ("impl-e2wFifo_idx", existT _ (SyntaxKind (Bit RegFileSz)) impl_e2wfifo_idxv)
     :: ("impl-e2wFifo_val", existT _ (SyntaxKind (Bit DataSz)) impl_e2wfifo_valv)
     :: ("impl-e2wFifo_valid", existT _ (SyntaxKind Bool) impl_e2wfifo_validv )
     :: ("pgm", existT _ (SyntaxKind (Array NumInstrs (Bit InstrSz))) pgmv)
     :: ("impl-rf", existT _ (SyntaxKind (Array 32 (Bit DataSz))) impl_rf_v)
     :: nil ;

     Hsregs: sregs =
      ("spec-decoder_pc", existT _ (SyntaxKind (Bit PgmSz)) spec_pcv)
	   :: ("spec-decoder_addr", existT _ (SyntaxKind (Bit AddrSz)) spec_decoder_addrv)
	      :: ("spec-decoder_arithOp", existT _ (SyntaxKind OpArithK) spec_decoder_arithOpv)
		 :: ("spec-decoder_op", existT _ (SyntaxKind OpK) spec_decoder_opv)
		    :: ("spec-decoder_dst", existT _ (SyntaxKind (Bit (Nat.log2_up 32))) spec_decoder_dstv)
		       :: ("spec-decoder_src1", existT _ (SyntaxKind (Bit (Nat.log2_up 32))) spec_decoder_src1v)
			  :: ("spec-decoder_src2", existT _ (SyntaxKind (Bit (Nat.log2_up 32))) spec_decoder_src2v)
			     :: ("spec-exec_dst", existT _ (SyntaxKind (Bit (Nat.log2_up 32))) spec_exec_dstv)
				:: ("spec-exec_val", existT _ (SyntaxKind (Bit DataSz)) spec_exec_valv)
				   :: ("spec-refproc_state", existT _ (SyntaxKind (Bit 2)) spec_refproc_statev)
				      :: ("pgm", existT _ (SyntaxKind (Array NumInstrs (Bit InstrSz))) pgmv)
					 :: ("spec-rf", existT _ (SyntaxKind (Array 32 (Bit DataSz))) spec_rf_v)
					    :: nil ;

     Hpcinv: (impl_d2efifo_validv = true ) -> (impl_pcv = impl_d2efifo_pcv ^+ $1 /\ spec_pcv = impl_d2efifo_pcv) ;
     Hpcinv_decode: (impl_d2efifo_validv = false ) -> (impl_pcv = spec_pcv) ;
     Hdeinv: decexec_d2e_inv dec pgmv impl_pcv
		 impl_d2efifo_pcv
		 impl_d2efifo_validv
		 impl_d2efifo_addrv
		 impl_d2efifo_arithopv
		 impl_d2efifo_opv
		 impl_d2efifo_pcv
		 impl_d2efifo_dstv 
		 impl_d2efifo_src1v
		 impl_d2efifo_src2v ;

     He2w_valid: impl_e2wfifo_validv = true -> (spec_refproc_statev = (natToWord 2 1)%kami_expr) ;
     He2w_val:   impl_e2wfifo_validv = true ->  impl_e2wfifo_valv = spec_exec_valv ;
     He2w_idx:   impl_e2wfifo_validv = true ->  impl_e2wfifo_idxv = spec_exec_dstv
   }.

  Definition decexecSepWf := {| baseModule := (getFlat (decexecSep dec execStub)) ;
			        wfBaseModule := ltac:(discharge_wf)  |}.

  Definition decexecWf := {| baseModule := (getFlat (multicycle dec execStub)) ;
			     wfBaseModule := ltac:(discharge_wf)  |}.


  Ltac andb_true_intro_split := apply andb_true_intro; split.

  Lemma findStr A B (decidable: forall a1 a2, {a1 = a2} + {a1 <> a2}):
    forall (ls: list (A * B)),
    forall x, In x ls <->
	      In x (filter (fun t => getBool (decidable (fst x) (fst t))) ls).
  Proof.
    induction ls; simpl; split; auto; intros.
    - destruct H; [subst|]; auto.
      + destruct (decidable (fst x) (fst x)) ; simpl in *; tauto.
      + apply IHls in H.
	destruct (decidable (fst x) (fst a)) ; simpl in *; auto.
    - destruct (decidable (fst x) (fst a)) ; simpl in *.
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

  Ltac discharge_init_forall2 :=
    repeat (match goal with
	    | H: _ |- Forall2 ?p ?l1 ?l2 => apply Forall2_cons; simpl
	    | H: _ |- Forall2 ?p nil nil => apply Forall2_nil
	    | H: _ |- ?a /\ ?b => split
	    | H: _ |- _ :: _ = _ :: _ => repeat f_equal
	    | H: _ |- ?a = ?a => reflexivity
	    | H: _ |- exists _, _ => exists eq_refl
	    end).

(* repeat apply Forall2_cons. simpl; try (split; [try congruence | exists eq_refl; reflexivity; eauto]). *)
Theorem pipelined_multicycle_ok:
    TraceInclusion decexecSepWf
                   decexecWf.
  Proof.
  discharge_simulationGeneral mySimRel.
  + admit.
  + reflexivity.
  + (* decode rule *)
    right. exists "spec-decode". eexists. split.
    * (* simRel oImp' oSpec *)
      left. trivial.
    *  eexists. eexists. split.
     ** foo. discharge_SemAction. 

(*
  bk_discharge_simulationZero mySimRel.
  + 
    repeat (match goal with
           | H: RegT |- _ => let nm := fresh "nm" in
                             let k := fresh "k" in
                             let val := fresh "val" in
                             destruct H as [nm [k val]]
           end).
    simpl in *. subst.
   exists (("spec-decoder_pc",
     existT (fullType type)
       (SyntaxKind (Bit PgmSz))
       (wzero PgmSz))
      :: ("spec-decoder_addr",
           existT (fullType type)
             (SyntaxKind
                (Bit AddrSz))
                   (wzero AddrSz))
           :: ("spec-decoder_arithOp",
              existT (fullType type)
                (SyntaxKind
                   OpArithK)
                      (wzero 2))
              :: ("spec-decoder_op",
                 existT
                   (fullType type)
                   (SyntaxKind OpK)
                      (wzero 2))
                 :: ("spec-decoder_dst",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Bit
                      (Nat.log2_up
                      32)))
                      (wzero
                      (Nat.log2_up
                      32)))
                    :: 
                    ("spec-decoder_src1",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Bit
                      (Nat.log2_up
                      32)))
                      (wzero
                      (Nat.log2_up
                      32)))
                    :: 
                    ("spec-decoder_src2",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Bit
                      (Nat.log2_up
                      32)))
                      (wzero
                      (Nat.log2_up
                      32)))
                    :: 
                    ("spec-exec_dst",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Bit
                      (Nat.log2_up
                      32)))
                      (wzero
                      (Nat.log2_up
                      32)))
                    :: 
                    ("spec-exec_val",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Bit DataSz))
                      (wzero
                      DataSz))
                    :: 
                    ("spec-refproc_state",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Bit 2))
                      (wzero 2))
                    :: 
                    ("pgm",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Array
                      NumInstrs
                      (Bit InstrSz)))
                      val0)
                    :: 
                    ("spec-rf",
                    existT
                      (fullType type)
                      (SyntaxKind
                      (Array 32
                      (Bit DataSz)))
                      (fun
                      _ : Fin.t 32
                      =>
                      wzero DataSz))
                    :: nil).
   rewrite H14. rewrite H25.
   simpl. split.
   * discharge_init_forall2.
   * econstructor.
    ** trivial.
    ** discharge_init_forall2.
    ** discharge_init_forall2.
    ** foo.
    ** foo. (* val12 = $0 = wzero PgmSz *)
    ** econstructor. foo. discharge_init_forall2. foo. foo. foo. foo. foo. foo.
    ** foo.
    ** foo.
    ** foo.
  + (* decode rule *)
    right. exists "spec-decode". eexists. split.
    * (* simRel oImp' oSpec *)
      left. trivial.
    *  eexists. eexists. split.
     ** foo. discharge_SemAction.
      *** admit.
      *** admit.
      *** admit.
    ** 

  + (* arith rule *)
    destruct H1.
    right. exists "spec-decexecArith". eexists. split.
    * left. trivial.
    * (* reads spec *) eexists. (* updates spec *) eexists. split.
     **

 rewrite Hsregs. discharge_SemAction. foo.
rewrite andb_true_iff. split.
      *** destruct Hdeinv. reflexivity. 
          destruct Hpcinv. reflexivity. rewrite H3. foo. simpl in H. apply H.
      *** rewrite negb_true_iff. reflexivity.

     ** rewrite Hsregs. rewrite Hiregs. simpl.
evar (impl_d2efifo_validv0 : bool).
econstructor 1 with (impl_d2efifo_validv := impl_d2efifo_validv0).
     *** repeat f_equal. unfold impl_d2efifo_validv0. trivial.
     *** repeat f_equal.
     *** intro. inv H1.
     *** unfold impl_d2efifo_validv0. intro. foo. destruct Hpcinv.
         **** reflexivity.
         **** rewrite H1. rewrite H0. rewrite wzero_wplus. reflexivity.
     *** econstructor. foo. foo.
     *** reflexivity.
     *** intro; reflexivity.
     *** intro. destruct Hdeinv. foo.
      **** foo. simpl. destruct Hpcinv. reflexivity. rewrite H1. reflexivity. *)

Qed.
End DecExecSepOk.
