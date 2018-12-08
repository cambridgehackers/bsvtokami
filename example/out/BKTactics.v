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