Require Import Kami.
Require Import Kami.Lib.Struct.
Require Import Bool Arith String Nat ZArith.

Fixpoint toBinaryP (p: positive) : string :=
  match p with
  | xI p' => String "1" (toBinaryP p')
  | xO p' => String "0" (toBinaryP p')
  | xH => ""
  end.

Definition toBinaryN (n: N): string :=
  match n with
  | N0 => "0"
  | Npos p => toBinaryP p
  end.

Definition toBinaryString (n: nat) := (toBinaryN (N.of_nat n)).

Record ModuleInstance intT :=
    { instance : string;
      module : Modules;
      interface : intT;
    }.

Definition ExtCall := string.

Definition bitlt (x : nat) (y: nat): bool := (Nat.ltb x y).

(** * Notation for BSV to Kami modules *)

Inductive BKElt :=
| BKRegister (_ : RegInitT)
| BKRule (_ : Attribute (Action Void))
| BKMeth (_ : DefMethT)
| BKMod (_ : list Modules)
| BKBlock (_ : InBKModule)

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
    | BKBlock m =>
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

Notation "'BKSTMTS' { s1 'with' .. 'with' sN }" :=
  (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk NilInBKModule) ..)
    (at level 0, only parsing).

Notation "'LOOP' { s1 'with' .. 'with' sN } SL" :=
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
