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
