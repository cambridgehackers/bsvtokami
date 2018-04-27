Require Import Kami.
Require Import Kami.Lib.Struct.
Require Import Bool Arith.

Fixpoint appendInModule (im1: InModule) (im2: InModule) : InModule :=
    match im1 with
    | NilInModule => im2
    | ConsInModule e im1' => ConsInModule e (appendInModule im1' im2)
end.

Definition moduleStatement stmt: InModule :=
    (ConsInModule stmt NilInModule).

Notation "'MODULESTMTS' { s1 'with' .. 'with' sN }" :=
  (makeModule (appendInModule s1 .. (appendInModule sN NilInModule) ..))
    (at level 0, only parsing).

Notation "'STMTS' { s1 'with' .. 'with' sN }" :=
  (appendInModule s1 .. (appendInModule sN NilInModule) ..)
    (at level 0, only parsing).

Definition bitlt (x : nat) (y: nat): bool := (Nat.ltb x y).

(** * Notation for BSV to Kami modules *)

Inductive BKElt :=
| BKRegister (_ : RegInitT)
| BKRule (_ : Attribute (Action Void))
| BKMeth (_ : DefMethT)
| BKMod (_ : list Modules)
| BKElts (_ : InBKModule)

with InBKModule :=
| NilInBKModule
| ConsInBKModule (_ : BKElt) (_ : InBKModule).

Fixpoint makeBKModule' (im : InBKModule) :=
  match im with
  | NilInBKModule => (nil, nil, nil, nil)
  | ConsInBKModule e i =>
    let '(iregs, irules, imeths, imods) := makeBKModule' i in
    match e with
    | BKRegister mreg => (mreg :: iregs, irules, imeths, imods)
    | BKRule mrule => (iregs, mrule :: irules, imeths, imods)
    | BKMeth mmeth => (iregs, irules, mmeth :: imeths, imods)
    | BKMod mmods => (iregs, irules, imeths, mmods ++ imods)
    | BKElts m =>
      let '(mregs, mrules, mmeths, mmods) := makeBKModule' m in
      (mregs ++ iregs, mrules ++ irules, mmeths ++ imeths, mmods ++ imods)
    end
  end.

Fixpoint concatModules (m: Modules) (lm: list Modules) :=
  match lm with
  | nil => m
  | m' :: lm' => concatModules (ConcatMod m m') lm'
  end.

Definition makeBKModule (im : InBKModule) :=
  let '(regs, rules, meths, mods) := makeBKModule' im in
  concatModules (Mod regs rules meths) mods.

(* * BSV to Kami Notation *)

Delimit Scope bk_scope with bk.

Notation "'STMTSR' { s1 'with' .. 'with' sN } SL" :=
  (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk SL%bk) ..)
    (at level 0, only parsing).

Notation "'RegisterN' name : type <- 'Default'" :=
  (BKRegister (Build_Attribute name (RegInitDefault type)))
    (at level 0, name at level 0, type at level 0) : bk_scope.

Notation "'RegisterN' name : type <- init" :=
  (BKRegister (Build_Attribute name (RegInitCustom (existT ConstFullT type init))))
    (at level 0, name at level 0, type at level 0, init at level 0) : bk_scope.

Notation "'Register' name : type <- 'Default'" :=
  (BKRegister (Build_Attribute name (RegInitDefault (SyntaxKind type))))
    (at level 0, name at level 0, type at level 0) : bk_scope.

Notation "'Register' name : type <- init" :=
  (BKRegister (Build_Attribute name (RegInitCustom (existT ConstFullT (SyntaxKind type) (makeConst init)))))
    (at level 0, name at level 0, type at level 0, init at level 0) : bk_scope.

Notation "'Method' name () : retT := c" :=
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := Void; ret := retT |}
                                   (fun ty => fun _ : ty Void =>
                                                (c)%kami_action : ActionT ty retT))))
    (at level 0, name at level 0) : bk_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := dom; ret := retT |}
                                   (fun ty => fun param : ty dom =>
                                                (c)%kami_action : ActionT ty retT))))
    (at level 0, name at level 0, param at level 0, dom at level 0) : bk_scope.

Notation "'Rule' name := c" :=
  (BKRule (Build_Attribute name (fun ty => c%kami_action : ActionT ty Void)))
    (at level 0, name at level 0) : bk_scope.

Notation "'BKMODULE' { s1 'with' .. 'with' sN }" :=
  (makeBKModule (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk NilInBKModule) ..))
    (at level 0, only parsing).
