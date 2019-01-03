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
             (pcv: fullType type (SyntaxKind (Bit PgmSz)))
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2eeltv: fullType type (SyntaxKind D2E)) :=
    d2efullv = true -> pcv = d2eeltv F5 ^+ $1.
  
  Definition decexec_d2e_inv
             (pgmv: fullType type (SyntaxKind (Array NumInstrs (Bit InstrSz))))
             (d2efullv: fullType type (SyntaxKind Bool))
             (d2eeltv: fullType type (SyntaxKind D2E)) :=
    d2efullv = true ->
    let pc := d2eeltv F5 in
    let inst := evalExpr (ReadArray (Var type (SyntaxKind _) pgmv) (Var type (SyntaxKind (Bit PgmSz)) pc )) in
    d2eeltv F4 = evalExpr (getOp kamidec _ inst) /\
    d2eeltv F2 = evalExpr (getArithOp kamidec _ inst) /\
    d2eeltv F6 = evalExpr (getSrc1 kamidec _ inst) /\
    d2eeltv F7 = evalExpr (getSrc2 kamidec _ inst) /\
    d2eeltv F3 = evalExpr (getDst kamidec _ inst) /\
    d2eeltv F1 = evalExpr (getAddr kamidec _ inst).

  Record decexec_inv (o: RegsT): Prop :=
    { pcv: fullType type (SyntaxKind (Bit PgmSz)) ;
      Hpcv: findReg "decexec-pc"%string o = Some (existT _ _ pcv) ;
      pgmv: fullType type (SyntaxKind (Array NumInstrs (Bit InstrSz))) ;
      Hpgmv: findReg "pgm"%string o = Some (existT _ _ pgmv) ;
      d2efullv: fullType type (SyntaxKind Bool) ;
      Hd2efullv: findReg "decexec-d2eFifo_valid"%string o = Some (existT _ _ d2efullv) ;
      d2eeltv: fullType type (SyntaxKind D2E) ;
      Hd2eeltv: findReg "decexec-d2eFifo_reg"%string o = Some (existT _ _ d2eeltv) ;

      Hpcinv: decexec_pc_inv pcv d2efullv d2eeltv ;
      Hdeinv: decexec_d2e_inv pgmv d2efullv d2eeltv
    }.

  Definition decexec_inv_jeh (o: RegsT): Prop :=
    match findReg "decexec-pc" o,
          findReg "pgm" o,
          findReg "decexec-d2eFifo_valid" o,
          findReg "decexec-d2eFifo_reg" o with
    | (Some pcreg), (Some pgmreg), (Some validreg), (Some fiforeg) => True
 (*     (decexec_pc_inv (projT2 pcreg) (projT2 validreg) (projT2 fiforeg))
      /\ (decexec_d2e_inv (projT2 pgmreg) (projT2 validreg) (projT2 fiforeg)) *)
    | _, _, _, _ => False
    end.

  (* Make sure to register all invariant-related definitions in the [InvDefs]
   * hint database, in order for Kami invariant-solving tactics to unfold them
   * automatically. *)
  Hint Unfold decexec_pc_inv decexec_d2e_inv: InvDefs.

Definition mySimRel (iregs sregs: RegsT) :=
  findReg "pgm" iregs = findReg "pgm" sregs
/\ decexec_inv iregs
/\ getKindAttr iregs =
   ("decexec-d2eFifo_reg", SyntaxKind D2E)
  :: ("decexec-d2eFifo_valid", SyntaxKind Bool)
    :: ("decexec-pc", SyntaxKind (Bit PgmSz))
      :: ("decexec-e2wFifo_reg", SyntaxKind E2W)
	:: ("decexec-e2wFifo_valid", SyntaxKind Bool)
	  :: ("pgm", SyntaxKind (Array NumInstrs (Bit InstrSz)))
	    :: ("decexec-regs", SyntaxKind (Array 32 (Bit DataSz)))
	      :: ("decexec-sbFlags", SyntaxKind (Array 32 Bool))
                :: nil
  /\ getKindAttr sregs =
  ("decexec-e2wFifo_reg", SyntaxKind E2W)
    :: ("decexec-e2wFifo_valid", SyntaxKind Bool)
      :: ("decexec-pc", SyntaxKind (Bit PgmSz))
	:: ("pgm", SyntaxKind (Array NumInstrs (Bit InstrSz)))
	  :: ("decexec-regs", SyntaxKind (Array 32 (Bit DataSz)))
	    :: ("decexec-sbFlags", SyntaxKind (Array 32 Bool))
	      :: nil.

Check mySimRel.
End DecExec.

  (* In order to prove invariants, we need to provide two customized tactics:
   * one is for destructing invariants for the current state
   * ([decexec_inv_dest_tac]), and the other is for constructing invariants for
   * the next state ([decexec_inv_constr_tac]). *)
Ltac decexec_inv_dest_tac :=
    unfold getAllRegisters, (* decexecSepInl, *) projT1;
    try match goal with
        | [ H: decexec_inv _ |- _ ] => destruct H
        | [ |- decexec_inv _ ] => destruct decexec_inv
        end.

Definition decexecSepWf := {| baseModule := (getFlat (decexecSep decStub execStub)) ;
				     wfBaseModule := ltac:(discharge_wf)  |}.

Theorem decexec_wfBaseModule:
  WfBaseModule
   (getFlat
      (decexec decStub execStub)).
Proof.
  discharge_wf.
Qed.

Definition decexecWf := {| baseModule := (getFlat (decexec decStub execStub)) ;
				     wfBaseModule := ltac:(discharge_wf)  |}.

Section DecExecSepOk.
Theorem decexecSep_ok:
    TraceInclusion decexecSepWf
                   decexecWf.
  Proof.
  discharge_appendage.
  discharge_simulationGeneral (mySimRel decStub) ltac:(discharge_DisjKey).
  + discharge_NoSelfCall.
  + unfold mySimRel in H. destruct H, H0, H1. rewrite <- H2. reflexivity.
  + unfold mySimRel in H. destruct H, H0, H1. rewrite <- H1. reflexivity.
  + unfold mySimRel. exists (x2 :: x3 ::x1 :: x4 :: x5 :: x6 :: nil). split.
   ++ repeat apply Forall2_cons; simpl; try (split; [try congruence | eexists; eauto]).
      apply Forall2_nil.
   ++ split.
   +++ unfold findReg. rewrite H3, H2, H4, H5, H6, H7, H1, H. econstructor.
   +++ split.
   ++++ econstructor.
   * unfold findReg. rewrite H3, H2, H4, H5, H6, H7, H1, H.
simpl. admit. (* need ?pcv for x2 *)
   * unfold findReg. rewrite H3, H2, H4, H5, H6, H7, H1, H. simpl.
     admit. (* need ?pgmv for x4 *)
   * unfold findReg. rewrite H3, H2, H4, H5, H6, H7, H1, H. simpl.
     admit. (* need ?d2efullv for x0 *)
   * unfold findReg. rewrite H3, H2, H4, H5, H6, H7, H1, H. simpl.
     admit.
   * unfold decexec_pc_inv. intro. trivial.
   * unfold decexec_d2e_inv.
     simpl. intro. repeat split; admit. (* need ?d2eltv and ?d2efullv *)
   ++++ repeat split; unfold getKindAttr; congruence.
  + unfold mySimRel. left. repeat split.
   ++ unfold mySimRel in H1. repeat destruct H1. apply findReg_doUpdRegs_unchanged with (s := "pgm").
      unfold findReg. econstructor.
      assert (findReg "pgm" oImp = Some (existT (fullType type)
         (SyntaxKind (Array NumInstrs (Bit InstrSz))) x2)).
      +++ apply findRegs_Some.
      ++++ admit. (* nodup (map fst oImp) *)
      ++++ apply H4.
      +++ rewrite H1. admit. (* findReg "pgm" oImp <> None *)
   ++ econstructor.
    +++ apply findReg_doUpdRegs_updated with (s := "decexec-pc") (t := (SyntaxKind (Bit PgmSz))).
     * simpl. trivial. (* ?pcv0 *)
     * congruence.
    +++ admit. (* pgm *)
    +++ apply findReg_doUpdRegs_updated with (t := (SyntaxKind Bool)).
     * simpl. trivial.
     * congruence.
    +++ apply findReg_doUpdRegs_updated with (t := (SyntaxKind D2E)).
     * simpl. trivial.
     * congruence.
    +++ unfold decexec_pc_inv. simpl. intro. 
        rewrite wzero_wplus with (sz := PgmSz) (w := x1). reflexivity.
    +++ unfold decexec_d2e_inv. simpl. intro. repeat split; reflexivity.
   ++ Search (getKindAttr (doUpdRegs _ _ )).
      rewrite <- getKindAttr_doUpdRegs.
     +++ unfold mySimRel in H1. destruct H1, H2, H13. rewrite H13. reflexivity.
     +++ assert (map fst oImp = map fst (getKindAttr oImp)).
      * admit.
      * rewrite H2. unfold mySimRel in H1. destruct H1, H13, H14. rewrite H14. simpl. 
        (* repeat apply NoDup_cons; simpl. Search (_ -> False). *)
        admit.
    +++ simpl. trivial. admit. (* NoDup *)
    +++ simpl. admit.
    ++ unfold mySimRel in H1. destruct H1, H2, H13. rewrite H14. reflexivity.
  + admit.
  + admit.
  + right. exists "decexec-decexecArith". eexists. split.
    * left. trivial.
    * exists oSpec. exists nil. split.
      admit.
      admit.
  + right. exists "decexec-decexecArith". eexists. split.
   * left. trivial.
   * exists oSpec. exists nil. split.
     ** simpl. Search (SemAction _). (* what to do here with SemAction *) admit. (* SemAction *)
     ** admit. (* mySimRel *)
Admitted.
