Require Import Kami.All.
Require Import Bsvtokami.
Require Import FIFO.
Require Import ProcMemSpec PipelinedProc ProcDecExec.
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

  Local Definition dec: ProcMemSpec.Decoder := mkDecoder kamidec "dec".
  Local Definition exec: ProcMemSpec.Executer := mkExecuter kamiexec "exec".

  Local Definition decexec : Mod := (Empty'mod (ProcDecExec.mkDecExec "decexec" kamidec kamiexec)).
  Hint Unfold decexec: ModuleDefs.

  Local Definition decexecSep : Mod := (Empty'mod (ProcDecExec.mkDecExecSep  "decexec" kamidec kamiexec)).
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
             (ipcv: fullType type (SyntaxKind (Bit PgmSz)))
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2e_pcv:      word PgmSz) :=
             (d2efullv = true ) -> (ipcv = d2e_pcv ^+ $1 ).
  
  Definition decexec_d2e_inv
             (pgmv: fullType type (SyntaxKind (Array NumInstrs (Bit InstrSz))))
             (ipcv:         word PgmSz)
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
    ipcv = (wzero PgmSz ^+ d2e_pcv ^+ $1)
    ).


  (* Make sure to register all invariant-related definitions in the [InvDefs]
   * hint database, in order for Kami invariant-solving tactics to unfold them
   * automatically. *)
  Hint Unfold decexec_pc_inv decexec_d2e_inv: InvDefs.

End DecExec.

Record mySimRel (dec : Decoder) (iregs sregs: RegsT): Prop :=
 {
   pgmv: (Fin.t NumInstrs -> word DataSz) ;

   ide_fifo_validv: bool ;
   ipcv: word PgmSz ;
   ide_e2wfifo_validv: bool ;
   ide_e2wfifo_idxv: fullType type (SyntaxKind (Bit RegFileSz)) ;
   ide_e2wfifo_valv: fullType type (SyntaxKind (Bit DataSz)) ;
   ideregv: fullType type (SyntaxKind (Array 32 (Bit DataSz))) ;
   (* idesbflagsv: fullType type (SyntaxKind (Array 32 Bool)) ; *)

   spcv: word PgmSz ;
   sde_e2wfifo_validv: bool ;
   sde_e2wfifo_idxv: fullType type (SyntaxKind (Bit RegFileSz)) ;
   sde_e2wfifo_valv: fullType type (SyntaxKind (Bit DataSz)) ;
   sderegv: (Fin.t 32 -> word DataSz) ;
   (* sdesbflagsv: (Fin.t 32 -> bool) ; *)

   ide_fifo_addrv    : word AddrSz ;
   ide_fifo_arithopv : fullType type (SyntaxKind OpArithK) ;
   ide_fifo_opv      : fullType type (SyntaxKind OpK) ;
   ide_fifo_pcv      : word PgmSz ;
   ide_fifo_dstv     : word RegFileSz ;
   ide_fifo_src1v    : word RegFileSz ;
   ide_fifo_src2v    : word RegFileSz ;

   Hpcinv: (ide_fifo_validv = true ) -> (ipcv = ide_fifo_pcv ^+ $1 ) ;
   Hdeinv: decexec_d2e_inv dec pgmv ipcv
               ide_fifo_pcv
               ide_fifo_validv
               ide_fifo_addrv
               ide_fifo_arithopv
               ide_fifo_opv
               ide_fifo_pcv
               ide_fifo_dstv 
               ide_fifo_src1v
               ide_fifo_src2v ;

   Hiregs: iregs =
   ("decexec-pc", existT _ (SyntaxKind (Bit PgmSz)) ipcv)
   :: ("decexec-d2eFifo_valid", existT _ (SyntaxKind Bool) ide_fifo_validv)
   :: ("decexec-d2eFifo_addr", existT _ (SyntaxKind (Bit AddrSz)) ide_fifo_addrv)
   :: ("decexec-d2eFifo_arithOp", existT _ (SyntaxKind OpArithK) ide_fifo_arithopv)
   :: ("decexec-d2eFifo_op", existT _ (SyntaxKind OpK) ide_fifo_opv)
   :: ("decexec-d2eFifo_pc", existT _ (SyntaxKind (Bit PgmSz)) ide_fifo_pcv)
   :: ("decexec-d2eFifo_dst", existT _ (SyntaxKind (Bit RegFileSz)) ide_fifo_dstv)
   :: ("decexec-d2eFifo_src1", existT _ (SyntaxKind (Bit RegFileSz)) ide_fifo_src1v)
   :: ("decexec-d2eFifo_src2", existT _ (SyntaxKind (Bit RegFileSz)) ide_fifo_src2v)
   :: ("decexec-e2wFifo_idx", existT _ (SyntaxKind (Bit RegFileSz)) ide_e2wfifo_idxv)
   :: ("decexec-e2wFifo_val", existT _ (SyntaxKind (Bit DataSz)) ide_e2wfifo_valv)
   :: ("decexec-e2wFifo_valid", existT _ (SyntaxKind Bool) ide_e2wfifo_validv )
   :: ("pgm", existT _ (SyntaxKind (Array NumInstrs (Bit InstrSz))) pgmv)
   :: ("decexec-regs", existT _ (SyntaxKind (Array 32 (Bit DataSz))) sderegv)
   (* :: ("decexec-sbFlags", existT _ (SyntaxKind (Array 32 Bool)) sdesbflagsv) *)
   :: nil ;

   Hsregs: sregs =
   ("decexec-e2wFifo_idx", existT (fullType type) (SyntaxKind (Bit RegFileSz)) sde_e2wfifo_idxv)
    :: ("decexec-e2wFifo_val", existT (fullType type) (SyntaxKind (Bit DataSz)) sde_e2wfifo_valv)
    :: ("decexec-e2wFifo_valid", existT (fullType type) (SyntaxKind Bool) sde_e2wfifo_validv )
    :: ("decexec-pc", existT (fullType type) (SyntaxKind (Bit PgmSz)) spcv)
    :: ("pgm", existT (fullType type) (SyntaxKind (Array NumInstrs (Bit InstrSz))) pgmv)
    :: ("decexec-regs", existT (fullType type) (SyntaxKind (Array 32 (Bit DataSz))) ideregv)
    (* :: ("decexec-sbFlags", existT (fullType type) (SyntaxKind (Array 32 Bool)) idesbflagsv) *)
    :: nil

 }.


Section DecExecSepOk.
  Variable decoder: Decoder.Decoder.
  
  Definition decexecSepWf := {| baseModule := (getFlat (decexecSep decoder execStub)) ;
			        wfBaseModule := ltac:(discharge_wf)  |}.

  Definition decexecWf := {| baseModule := (getFlat (decexec decoder execStub)) ;
			     wfBaseModule := ltac:(discharge_wf)  |}.


Ltac unfold_mySimRel :=
  match goal with
   | [ |- ?goal ] => idtac "mySimRel" ; simple refine goal
   end.

Ltac discharge_findreg :=
   match goal with
   | [ |- findReg _ _ = _ ] => idtac "findreg"; unfold findReg 
   end; repeat discharge_string_dec.

Ltac discharge_simulationZero mySimRel :=
  apply _simulationZeroAction with (simRel := mySimRel) ; auto; simpl; intros;
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
Theorem decexecSep_ok:
    TraceInclusion decexecSepWf
                   decexecWf.
  Proof.
  discharge_appendage.
  discharge_simulationZero (mySimRel decoder).
  + destruct H. rewrite Hsregs. unfold getKindAttr. simpl. reflexivity.
  + destruct H. rewrite Hiregs. unfold getKindAttr. simpl. reflexivity.
  + exists (x8 :: x9 :: x10 :: x :: x11 :: x12:: nil). split.
   ++ repeat apply Forall2_cons; simpl; try (split; [try congruence | eexists; eauto]).
      apply Forall2_nil.
   ++ repeat match goal with
            | H: RegT |- _ => let m1 := fresh "nm" in
                              let m2 := fresh "knd" in
                              let m3 := fresh "v" in destruct H as [m1 [m2 m3]]
            end. simpl in *. subst.
           econstructor; try repeat f_equal; eauto.
    * rewrite H25. intro. inv H.
    * unfold decexec_d2e_inv. rewrite H25. intro. inv H.
  + (* decode rule *)
    left. split.
    * destruct H1. rewrite Hiregs. rewrite Hsregs. simpl. econstructor.
      ** eauto.
      ** eauto.
      ** destruct Hdeinv.
         *** admit.
         *** destruct H2. destruct H24. destruct H25. destruct H26. destruct H27.
             rewrite H1; rewrite H2; rewrite H24; rewrite H25; rewrite H26. rewrite H27; rewrite H28.
             simpl. admit.
      ** trivial.
    * reflexivity.
  + (* arith rule *)
    destruct H1.
    right. exists "decexec-decexecArith". eexists. split.
    * left. trivial.
    * exists oSpec. eexists. split.
     ** rewrite Hsregs. discharge_SemAction.
      ++ admit.
      ++ admit.
     ** rewrite Hsregs. rewrite Hiregs. simpl. econstructor.
     *** eauto.
     *** unfold decexec_pc_inv. intro. repeat split.
     *** admit.
     *** admit.
Admitted.
End DecExecSepOk.
