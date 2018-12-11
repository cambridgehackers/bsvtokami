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

    Record CoqDecoder :=
      { getOp: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind OpK) ;
        getArithOp: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind OpArithK) ;
        getSrc1: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
        getSrc2: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
        getDst: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
        getAddr: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit AddrSz))
      }.

Compute "CoqDecoder"%string.


(* Here we prove that merging the first two stages ([decoder] and [executer])
 * is correct by providing a refinement from [decexecSep] to [decexec]. *)
Section DecExec.

  Local Definition dataK := Bit ProcMemSpec.DataSz.
  Local Definition instK := Bit ProcMemSpec.InstrSz.

  Variables (coqdec: CoqDecoder)
            (kamidec: Decoder.Decoder)
            (kamiexec: Decoder.Executer)
            (sb: Scoreboard)
            (e2wfifo: FIFO)
            (rf: ProcRegs)
            (mem: Memory)
            (tohostmod: Mod)
            (pcInit : ConstT (Bit ProcMemSpec.PgmSz)).

  Local Definition pgm: RegFile := mkRegFileFull (Bit InstrSz) (Bit PgmSz) "pgm".
  Local Definition dec: ProcMemSpec.Decoder := mkDecoder kamidec "dec".
  Local Definition exec: ProcMemSpec.Executer := mkExecuter kamiexec "exec".
  Local Definition tohost: ToHost := (Build_ToHost tohostmod "tohost").

  Local Definition decexecSep : Mod := (Empty'mod (ProcDecExec.mkDecExecSep  "decexec" pgm dec exec tohost)).
  Hint Unfold decexecSep: ModuleDefs.

  Local Definition decexec : Mod := (Empty'mod (ProcDecExec.mkDecExec "decexec" pgm dec exec sb e2wfifo rf mem tohost)).
  Hint Unfold decexec: ModuleDefs.

  (* Local Definition decexecSepInl: {m: Mod & TraceInclusion (flatten_inline_remove decexecSep) m}.
  Proof.
    unfold TraceInclusion.
    intros.
    exists o1, ls1.
    repeat split; auto; intros; unfold nthProp2; intros; try destruct (nth_error ls1 i) ; auto; repeat split; intros; try firstorder.
  Defined.

  Local Definition decexecSepInl := decexecSepInl dec exec pcInit pgm.
*)
  Local Definition decexecSepInl := (flatten_inline_remove decexecSep).

  Set Printing Depth 10000.

  Print Assumptions decexec.
  Eval cbv in (flatten_inline_remove decexec).
  Compute "decexecInl"%string.

  Print Assumptions decexecSepInl.
  Eval cbv in (flatten_inline_remove decexecSep).
  Compute "decexecSepInl"%string.

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
    d2eeltv F4 = evalExpr (getOp coqdec _ inst) /\
    d2eeltv F2 = evalExpr (getArithOp coqdec _ inst) /\
    d2eeltv F6 = evalExpr (getSrc1 coqdec _ inst) /\
    d2eeltv F7 = evalExpr (getSrc2 coqdec _ inst) /\
    d2eeltv F3 = evalExpr (getDst coqdec _ inst) /\
    d2eeltv F1 = evalExpr (getAddr coqdec _ inst).

  Record decexec_inv (o: RegsT): Prop :=
    { pcv: fullType type (SyntaxKind (Bit PgmSz)) ;
      Hpcv: findReg "pc"%string o = Some (existT _ _ pcv) ;
      pgmv: fullType type (SyntaxKind (Array NumInstrs (Bit InstrSz))) ;
      Hpgmv: findReg "pgm"%string o = Some (existT _ _ pgmv) ;
      d2efullv: fullType type (SyntaxKind Bool) ;
      Hd2efullv: findReg "full.d2e"%string o = Some (existT _ _ d2efullv) ;
      d2eeltv: fullType type (SyntaxKind D2E) ;
      Hd2eeltv: findReg "elt.d2e"%string o = Some (existT _ _ d2eeltv) ;

      Hpcinv: decexec_pc_inv pcv d2efullv d2eeltv ;
      Hdeinv: decexec_d2e_inv pgmv d2efullv d2eeltv
    }.

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
        | [H: decexec_inv _ |- _] => destruct H
        end.

(*  Set Ltac Profiling.
Theorem decexec_ok:
    TraceInclusion (flatten_inline_remove decexecSep)
                   (flatten_inline_remove decexec).
  Proof.
  repeat autounfold with ModuleDefs.
  unfold flatten_inline_remove, getHidden, inlineAll_All_mod, getAllRegisters,
         getAllMethods, getAllRules, getRules, getRegisters, getMethods, app.
  unfold inlineAll_All.
  simpl.

  unfold inlineAll_Meths.

  unfold inlineSingle_Meths_pos.
  unfold inlineSingle_Meth.
  simpl.
  specialize (inlineSingle_Meths_pos _ 0) as INL0.

  Show Ltac Profile.
  unfold inlineSingle_Meths_pos.
  unfold inlineSingle_Meths_pos, nth_error, map.
  unfold inlineSingle_Meth.
  unfold inlineSingle. simpl.
  unfold inlineAll_Rules, inlineSingle_Rules_pos.
  simpl.
  unfold removeHides.
  simpl.
  do_inlining.
Admitted.

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

  Check (getRegFileRegisters _).
  Check (evalConstFullT _).
 (*  Definition rawInitRegs (init: list RegInitT) : RegsT :=
    map (fun r => match r with
        ) init.
*)

Print Trace.
Print FullLabel.
Search (FullLabel -> _).
Check (nat * string)%type.
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
