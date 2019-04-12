Require Import Bool String.
Require Import Kami.All.

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


(* Definition bk_inlineSingle_Meth (f : DefMethT) (meth : DefMethT): DefMethT :=
  let fn := fst f in
  let methname := fst meth in
  if string_dec fn methname
  then meth
  else (methname, inlineSingle f _).
*)

Theorem findReg_doUpdRegs_updated_not_none:
  forall (u o: RegsT) (s: string),
    None <> findReg s u
    -> None <> findReg s o
      -> None <> findReg s (doUpdRegs u o).
Proof.
Admitted.

Theorem findReg_doUpdRegs_updated:
  forall (u o: RegsT) (s: string) t v,
    findReg s u = v
    -> In (s, t) (getKindAttr o)
      -> findReg s (doUpdRegs u o) = v.
Proof.
Admitted.

Theorem findReg_doUpdRegs_unchanged_none:
  forall (u o: RegsT) (s: string),
    None = findReg s u
    -> None <> findReg s o
      -> None <> findReg s (doUpdRegs u o).
Proof.
Admitted.

Theorem findReg_doUpdRegs_unchanged:
  forall (u o: RegsT) (s: string),
    None = findReg s u
    -> findReg s o <> None
      -> findReg s (doUpdRegs u o) = findReg s o.
Proof.
Admitted.

Theorem findRegs_Some:
  forall u : list RegT,
  NoDup (map fst u) ->
  forall (s : string) (v : {x : FullKind & fullType type x}),
  In (s, v) u <-> findReg s u = Some v.
Proof.
Admitted.

Theorem InKindAttr:
  forall (s : string) t (o : RegsT),
    exists v,
      In (s, t) (getKindAttr o) -> In (s, existT (fullType type) t v) o.
Proof.
Admitted.

Local Ltac bk_clean_hyp :=
  repeat match goal with
         | H: @key_not_In _ _ _ _ |- _ => clear H
         end;
  repeat match goal with
         | H: DisjKey _ _ |- _ => apply DisjKeyWeak_same in H; [unfold DisjKeyWeak in H; simpl in H| apply string_dec]
         | H: In ?x ?ls |- _ =>
           apply (InFilter string_dec) in H; simpl in H; destruct H; [|exfalso; auto]
         | H: False |- _ => exfalso; apply H
         | H: (?A, ?B) = (?P, ?Q) |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           pose proof (f_equal fst H) as H1;
           pose proof (f_equal snd H) as H2;
           simpl in H1, H2;
           clear H
         | H: ?A = ?A |- _ => clear H
         | H: (?a ++ ?b)%string = (?a ++ ?c)%string |- _ => rewrite append_remove_prefix in H; subst
         | H: (?a ++ ?b)%string = (?c ++ ?b)%string |- _ => rewrite append_remove_suffix in H; subst
         | H: existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
         | H: ?A = ?B |- _ => discriminate
         | H: SemAction _ (convertLetExprSyntax_ActionT ?e) _ _ _ _ |- _ =>
           apply convertLetExprSyntax_ActionT_full in H; dest; subst
         end.

Local Ltac bk_destruct_Invariant mySimRel :=
  try match goal with
      | H: mySimRel _ _ |- _ => inv H
      end; bk_clean_hyp.

Ltac bk_discharge_simulationZero mySimRel :=
  apply simulationZeroAction with (simRel := mySimRel) ; auto; simpl; intros; bk_destruct_Invariant mySimRel; auto;
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
