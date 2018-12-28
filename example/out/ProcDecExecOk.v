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
  + unfold mySimRel. exists (("decexec-e2wFifo_reg",
    x2 :: x3 ::x1 :: x4 :: x5 :: x6 :: nil). repeat split.
   ++ repeat apply Forall2_cons.
    +++ rewrite H5. unfold fst. split.
     ++++ reflexivity.
     ++++ admit.
    +++ rewrite H6. unfold fst. split.
     ++++ reflexivity.
     ++++ admit.
    +++
Admitted.


Theorem findReg_doUpdRegs_updated:
  forall (u o: RegsT) (s: string),
    None <> findReg s u
    -> None <> findReg s o
      -> None <> findReg s (doUpdRegs u o).
Proof.
Admitted.

Theorem findReg_doUpdRegs_unchanged:
  forall (u o: RegsT) (s: string),
    None = findReg s u
    -> None <> findReg s o
      -> None <> findReg s (doUpdRegs u o).
Proof.
Admitted.


Lemma getKindAttr_doUpdRegs2 o:
  NoDup (map fst o) ->
  forall u,
    NoDup (map fst u) ->
    (forall s v, In (s, v) u -> In (s, projT1 v) (getKindAttr o)) ->
    getKindAttr (doUpdRegs u o) = getKindAttr o.
Proof.
  intros.
  setoid_rewrite getKindAttr_doUpdRegs'.
  rewrite forall_map; intros.
  case_eq (findReg (fst x) u) ; intros; auto.
  rewrite <- findRegs_Some in H3 ; auto.
  specialize (H1 _ _ H3).
  f_equal.
  destruct x ; simpl in *.
  apply (in_map (fun x => (fst x, projT1 (snd x)))) in H2; simpl in *.
  assert (sth: map fst o = map fst (getKindAttr o)). {
    rewrite map_map; simpl.
    assert (sth2: fst = fun x : RegT => fst x) by (extensionality x; intros; auto).
    rewrite sth2 ; auto.
  }
  rewrite sth in H.
  pose proof (@KeyMatching_gen _ _ (getKindAttr o) _ _ H H1 H2 eq_refl) ; simpl in *.
  inv H4; congruence.
Qed.


Section DecExecSepOk2.
Theorem decexecSep_ok2:
    TraceInclusion decexecSepWf
                   decexecWf.
  Proof.
  discharge_appendage.
  discharge_simulationGeneral (mySimRel) ltac:(discharge_DisjKey).
  + discharge_NoSelfCall.
  + unfold mySimRel in H. destruct H, H0, H1. rewrite <- H2. reflexivity.
  + unfold mySimRel in H. destruct H, H0, H1. rewrite <- H1. reflexivity.
  + unfold mySimRel. exists (x2 :: x3 ::x1 :: x4 :: x5 :: x6 :: nil). split.
  ++ apply Forall2_cons.
     rewrite H5. 
  +++ unfold fst. admit.
  +++ admit.
  ++ unfold findReg.
     rewrite H3, H2, H4, H5, H6, H7, H1. simpl. split.
  +++ reflexivity.
  +++ split.
  ++++ unfold decexec_inv. unfold findReg.
       rewrite H3, H2, H4, H5, H6, H7, H1, H. simpl. trivial.
  ++++ rewrite H3, H2, H4, H5, H6, H7, H1, H. 
       rewrite x14, x13, x12, x11, x10, x9, x8, x7.
       split.
       * reflexivity.
       * reflexivity.
  + left. split.
  ++ admit. (* fixme *)
  ++ reflexivity.
  + left. split.
  ++ admit.
  ++ reflexivity.
  + left. split.
  ++ admit.
  ++ admit. (* seems wrong *)
  + admit.
  + admit. (* tohost *)
Admitted.


Fixpoint getRegistersFromMod m :=
  match m with
  | Base bm => getRegisters bm
  | HideMeth m' meth => getRegistersFromMod m'
  | ConcatMod m1 m2 => getRegistersFromMod m1 ++ getRegistersFromMod m2
  end.

Section DecExecOk.
Theorem decexec_ok:
    TraceInclusion (decexec decStub execStub)
                   (decexec decStub execStub).
  Proof.

  unfold decexecSep, decexec.
  repeat autounfold with ModuleDefs. unfold Empty'mod.
  discharge_appendage.
  unfold TraceInclusion.
  intros.
  pose (o2 := o1).
  refine (ex_intro _ o1 _).
  pose (ls2 := ls1).
  refine (ex_intro _ ls1 _).
  split.
  - apply H.
  - split.
    + reflexivity.
    + Search (nthProp2 _ _ _).
      apply WeakInclusions_WeakInclusion.
      Search (WeakInclusions _ _).
      apply WeakInclusionsRefl.

Qed.
End DecExecOk.

Theorem decexecSep_wfBaseModule:
  WfBaseModule
   (getFlat
      (decexecSep decStub execStub)).
Proof.
  discharge_wf.
Qed.

End DecExecSepOk.

Theorem nodupregs_spec:
  (NoDup (map fst (getRegisters decexecWf))).
Proof.
  discharge_wf.
Qed.

Theorem noselfCalls_impl:
  NoSelfCallBaseModule (getFlat (decexecSep decStub execStub)).
Proof.
  discharge_NoSelfCall.
Qed.

(* fixme *)
Ltac kinv_eq :=
  repeat
    (first [ reflexivity
           (* | meqReify *)
           (* | findReify *)
           (* | fin_func_eq *)
           (* | apply existT_eq *)
           (* | apply pair_eq *)
    ]).


(* fixme too *)
Ltac kinv_red :=
  intros; repeat autounfold with InvDefs in *;
  dest; try subst (* ; kinv_simpl *).

  Ltac decexec_inv_constr_tac :=
    econstructor; intros;
    repeat (kinv_eq; kinv_red; eauto).

  Ltac decexec_inv_tac :=
    decexec_inv_dest_tac; decexec_inv_constr_tac.

  (* Now we are ready to prove the invariant!
   * Thanks to some Kami tactics, the proof will be highly automated. *)
  Lemma decexec_inv_ok':
(* what should init be *)
    forall init n,
      decexec_inv init ->
      Trace decexecSepInl init n ->
      (Forall (fun (lfl : list FullLabel) => Forall (fun (fl : FullLabel) => (decexec_inv (fst fl) )) lfl) n).
  Proof.
    (* Induction on [Trace] is the natural choice. *)
    induction 2.
    - (* Our custom destruction-construction tactic is used 
       * for the initial case as well. *)
      decexec_inv_tac; cbn in *; kinv_red.
    - (* [kinvert] is for inverting Kami steps. 
       * It may generate multiple subgoals corresponding to possible steps 
       * by a rule or a method. *)
      kinvert.
      + (* [kinv_dest_custom] is a tactic for proving invariants, and it takes
         * our customized tactic as a parameter. *)
        kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
      + kinv_dest_custom decexec_inv_tac.
  Qed.

  Lemma decexec_inv_ok:
    forall o,
      reachable o (projT1 decexecSepInl) ->
      decexec_inv o.
  Proof.
    intros; inv H; inv H0.
    eapply decexec_inv_ok'; eauto.
  Qed.

  (* Equipped with invariants, it is time to prove refinement.
   * Following the Kami verification flow, we will use a decomposition theorem.
   *)

  
  (* Finally the correctness proof!
   * The proof is highly automated as well, following a typical verification
   * flow and using the Kami tactics.
   *)
  Theorem decexec_ok:
    decexecSep dec exec pcInit pgmInit <<== decexec dec exec pcInit pgmInit.
  Proof.
    (* 1) Inlining: we already have an inlined module. 
     *    Let's use [kinline_refine_left] to substitute the LHS module 
     *    to the inlined one. *)
    kinline_refine_left decexecSepInl.

    (* 2) Decomposition: [kdecompose_nodefs] is mostly used for decomposition;
     *    it requires a target module without any methods. Indeed the module
     *    has no methods, since it is inlined. The tactic takes register and
     *    rule mappings as arguments. *)
    kdecompose_nodefs decexec_regMap decexec_ruleMap.

    (* 3) Simulation: we can add invariants using [kinv_add] and [kinv_add_end]
     *    before proving simulation. [kinvert] is used to invert Kami steps as
     *    well. [kinv_magic_with] is a high-level tactic to prove simulation for
     *    each possible step. It takes custom destruction and construction 
     *    tactics as arguments. For this proof, no construction tactics are
     *    required.
     *)
    kinv_add decexec_inv_ok.
    kinv_add_end.
    kinvert.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
    - kinv_magic_with decexec_inv_dest_tac idtac.
  Qed.

*)

End DecExec.
