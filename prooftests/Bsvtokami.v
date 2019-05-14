Require Import Kami.All.
Require Import Bool Arith String Nat ZArith ZArith.BinInt.

Definition Integer := nat.

(** * Notation for BSV to Kami modules *)

Inductive BKElt :=
| BKRegister (_ : RegInitT)
| BKRegAry (_ : list RegInitT)
| BKRule (_ : Attribute (Action Void))
| BKMeth (_ : DefMethT)
| BKMod (_ : list Mod)
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
    | BKRegAry reglist => (app reglist iregs, irules, imeths, imods)
    | BKRule mrule => (iregs, mrule :: irules, imeths, imods)
    | BKMeth mmeth => (iregs, irules, mmeth :: imeths, imods)
    | BKMod mmods => (iregs, irules, imeths, app mmods imods)
    | BKBlock m =>
      let '(mregs, mrules, mmeths, mmods) := makeBKModule' m in
      (app mregs iregs, app mrules irules, app mmeths imeths, app mmods imods)
    end
  end.

Fixpoint concatModules (m: Mod) (lm: list Mod) :=
  match lm with
  | nil => m
  | m' :: lm' => concatModules (ConcatMod m m') lm'
  end.

Definition makeBKModule (im : InBKModule) :=
  let '(regs, rules, meths, mods) := makeBKModule' im in
  concatModules (Base (BaseMod regs rules meths)) mods.

Hint Unfold concatModules : ModuleDefs.
Hint Unfold makeBKModule' : ModuleDefs.
Hint Unfold makeBKModule : ModuleDefs.
Hint Unfold app : ModuleDefs.

Fixpoint getOrderBK (im : InBKModule) :=
  match im with
  | NilInBKModule => nil
  | ConsInBKModule e i =>
    let rest := getOrderBK i in
    match e with
    | BKRule mrule => fst mrule :: rest
    | BKMeth mmeth => fst mmeth :: rest
    | _ => rest
    end
  end.

Fixpoint getOrderFromMod (m : Mod) := 
  match m with
  | Base bm => map fst (getRules bm) ++ map fst (getMethods bm)
  | HideMeth m' meth => getOrderFromMod m'
  | ConcatMod m1 m2 => getOrderFromMod m1 ++ getOrderFromMod m2
  end.

(* * BSV to Kami Notation *)

Delimit Scope bk_scope with bk.

(* Notation "$$ v" := (ConstBit v%kami) (at level 0) : bk_scope. *)

Notation "'BKSTMTS' { s1 'with' .. 'with' sN }" :=
  (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk NilInBKModule) ..)
    (at level 0, only parsing).

Notation "'LOOP' { s1 'with' .. 'with' sN } SL" :=
  (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk SL%bk) ..)
    (at level 0, only parsing).

Notation "'RegisterN' name : type <- init" :=
  (BKRegister (name%string, existT RegInitValT type (Some init)))
    (at level 12, name at level 99) : bk_scope.

Notation "'Register' name : type <- init" :=
  (BKRegister (name%string, existT RegInitValT (SyntaxKind type) (Init (makeConst init))))
    (at level 12, name at level 99) : bk_scope.

Notation "'RegisterU' name : type" :=
  (BKRegister (name%string, existT RegInitValT (SyntaxKind type) (Uninit _)))
    (at level 12, name at level 99) : bk_scope.

Notation "'Method' name () : retT := c" :=
  (BKMeth (name%string, existT MethodT (Void, retT)
                               (fun ty (_: ty Void) => c%kami_action : ActionT ty retT)))
    (at level 12, name at level 9) : bk_scope.

Notation "'Method' name ( param : dom ) : retT := c" :=
  (BKMeth (name%string, existT MethodT ( dom%kami, retT )
                               (fun ty ( param : ty dom%kami ) => c%kami_action : ActionT ty retT)))
    (at level 12, name at level 9, param at level 99) : bk_scope.
Notation "'Method1' name ( param : dom ) : retT := c" :=
  (BKMeth (name%string, existT MethodT ( dom%kami, retT )
                               (fun ty ( param : ty dom%kami ) => c%kami_action : ActionT ty retT)))
    (at level 12, name at level 9, param at level 99) : bk_scope.

Notation "'Rule' name := c" :=
  (BKRule (name%string, fun ty => (c)%kami_action : ActionT ty Void))
    (at level 12) : bk_scope.

Notation "'BKMODULE' { s1 'with' .. 'with' sN }" :=
  (makeBKModule (ConsInBKModule s1%bk .. (ConsInBKModule sN%bk NilInBKModule) ..))
    (at level 0, only parsing).

Notation "'BKCall' name : retT <- meth () ; cont " :=
  (MCall meth%string (Void, retT) (Const _ Default) (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0) : kami_action_scope.

Notation "'BKCall' name : retT <- meth ( a1 : a1T ) ; cont " :=
  (MCall meth%string (a1T, retT) a1%kami_expr (fun name => cont))
    (at level 12, right associativity, name at level 0, meth at level 0, a1 at level 99) : kami_action_scope.

Notation "'BKCall' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ; cont " :=
  (let argT := STRUCT_TYPE { "_1" :: a1T ; "_2" :: a2T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 })%kami_expr in
  (MCall meth%string (argT, retT) args%kami_expr (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0, a1 at level 99, a2 at level 99) : kami_action_scope.

Notation "'Method2' name ( p1 : d1 ) ( p2 : d2 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let dom := STRUCT_TYPE  { "_1" :: d1f ; "_2" :: d2f } in
  (BKMeth (name%string, existT MethodT (dom, retT)
                               (fun ty (param : ty dom) => 
				(LET p1 : d1g <- (#param @% "_1");
				 LET p2 : d2g <- (#param @% "_2");
				c%kami_action : ActionT ty retT)))))%kami_action
    (at level 12, name at level 9,
     p1 at level 99, p2 at level 99) : bk_scope.


Notation "'BKCall' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T ) ; cont " :=
  (let argT := STRUCT_TYPE { "_1" :: a1T ; "_2" :: a2T ; "_3" :: a3T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 })%kami_expr in
  (MCall meth%string (argT, retT) args%kami_expr (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99) : kami_action_scope.


Notation "'BKCall' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T ) ( a4 : a4T ); cont " :=
  (let argT := STRUCT_TYPE { "_1" :: a1T ; "_2" :: a2T ; "_3" :: a3T; "_4" :: a4T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 ; "_4" ::= a4 })%kami_expr in
  (MCall meth%string (argT, retT) args%kami_expr (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99, a4 at level 99) : kami_action_scope.


Notation "'BKCall' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T ) ( a4 : a4T ) ( a5 : a5T ); cont " :=
  (let argT := STRUCT_TYPE { "_1" :: a1T ; "_2" :: a2T ; "_3" :: a3T; "_4" :: a4T; "_5" :: a5T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 ; "_4" ::= a4 ; "_5" ::= a5 })%kami_expr in
  (MCall meth%string (argT, retT) args%kami_expr (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99, a4 at level 99, a5 at level 99) : kami_action_scope.


Notation "'BKCall' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T ) ( a4 : a4T ) ( a5 : a5T ) ( a6 : a6T ); cont " :=
  (let argT := STRUCT_TYPE { "_1" :: a1T ; "_2" :: a2T ; "_3" :: a3T; "_4" :: a4T; "_5" :: a5T; "_6" :: a6T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 ; "_4" ::= a4 ; "_5" ::= a5; "_6" ::= a6 })%kami_expr in
  (MCall meth%string (argT, retT) args%kami_expr (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99, a4 at level 99, a5 at level 99, a6 at level 99) : kami_action_scope.


Definition Maybe a := (STRUCT_TYPE { "$tag" :: (Bit 1) ; "Invalid" :: (Bit 1) ; "Valid" :: a }).

Definition castBits ty ni no (pf: ni = no) (e: Expr ty (SyntaxKind (Bit ni))) :=
  match pf in _ = Y return Expr ty (SyntaxKind (Bit Y)) with
    | eq_refl => e
  end.

Record Empty := {
    Empty'mod: Mod;
}.


Definition Tuple2 t1 t2 := (STRUCT_TYPE {
    "tpl_1" :: t1;
    "tpl_2" :: t2
}).

Record Reg := {
    Reg'mod: Mod;
    Reg'_read : string;
    Reg'_write : string;
}.
Hint Unfold Reg'mod : ModuleDefs.
Hint Unfold Reg'_read : ModuleDefs.
Hint Unfold Reg'_write : ModuleDefs.

Notation " s1 -- s2 " := ( s1 ++ "-" ++ s2 )%string (at level 9, s2 at level 9).

Module module'mkReg.
    Section Section'mkReg.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable v: ConstT a.
    Definition reg : string := instancePrefix--"reg".
    Local Open Scope kami_expr.
    Definition mkRegModule: Mod :=
      (BKMODULE {
           Register reg : a <- v
           with Method (instancePrefix--"_read") () : a :=
             Read v : a <- reg ;
           Ret #v

           with Method1 (instancePrefix--"_write") ( v : a ) : Void :=
             Write reg : a <- #v;
           Retv

         }). (* mkReg *)

(* Module mkReg type a -> Module#(Reg#(a)) return type Reg#(a) *)
    Definition mkReg := Build_Reg mkRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkReg.
End module'mkReg.

Definition mkReg := module'mkReg.mkReg.
Definition mkDWire := module'mkReg.mkReg.

Hint Unfold mkReg : ModuleDefs.
Hint Unfold module'mkReg.reg : ModuleDefs.
Hint Unfold module'mkReg.mkReg : ModuleDefs.
Hint Unfold module'mkReg.mkRegModule : ModuleDefs.

Module module'mkReadOnlyReg.
    Section Section'mkReadOnlyReg.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable v: ConstT a.
    Definition reg : string := instancePrefix--"reg".
    Definition mkReadOnlyRegModule: Mod :=
      (BKMODULE {
           Register reg : a <- v
           with Method (instancePrefix--"_read") () : a :=
             Read v : a <- reg ;
           Ret #v

           with Method1 (instancePrefix--"_write") (v : a) : Void :=
             Retv

         }). (* mkReadOnlyReg *)

(* Module mkReadOnlyReg type a -> Module#(Reg#(a)) return type Reg#(a) *)
    Definition mkReadOnlyReg := Build_Reg mkReadOnlyRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkReadOnlyReg.
End module'mkReadOnlyReg.

Definition mkReadOnlyReg := module'mkReadOnlyReg.mkReadOnlyReg.

Hint Unfold mkReadOnlyReg : ModuleDefs.
Hint Unfold module'mkReadOnlyReg.reg : ModuleDefs.
Hint Unfold module'mkReadOnlyReg.mkReadOnlyReg : ModuleDefs.
Hint Unfold module'mkReadOnlyReg.mkReadOnlyRegModule : ModuleDefs.


(* mkRegU *)
Module module'mkRegU.
    Section Section'mkRegU.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable v: ConstT a.
    Definition reg : string := instancePrefix--"reg".
    Definition mkRegUModule: Mod :=
        (BKMODULE {
           Register reg : a <- Default
           with Method (instancePrefix--"_read") () : a :=
             Read v : a <- reg ;
             Ret #v

           with Method1 (instancePrefix--"_write") ( v : a ) : Void :=
             Write reg : a <- #v;
             Retv

           }). (* mkRegU *)

(* Module mkRegU type a -> Module#(Reg#(a)) return type Reg#(a) *)
    Definition mkRegU := Build_Reg mkRegUModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkRegU.
End module'mkRegU.

Definition mkRegU := module'mkRegU.mkRegU.
Hint Unfold mkRegU : ModuleDefs.
Hint Unfold module'mkRegU.reg : ModuleDefs.
Hint Unfold module'mkRegU.mkRegU : ModuleDefs.
Hint Unfold module'mkRegU.mkRegUModule : ModuleDefs.

(* * interface RegFile#(index_t, data_t) *)
Record RegFile := {
    RegFile'mod: Mod;
    RegFile'upd : string;
    RegFile'sub : string;
}.
Hint Unfold RegFile'mod : ModuleDefs.
Hint Unfold RegFile'upd : ModuleDefs.
Hint Unfold RegFile'sub : ModuleDefs.

Module module'mkRegFileFull.
    Section Section'mkRegFileFull.
    Variable data_t : Kind.
    Variable index_t : Kind.
    Variable instancePrefix: string.
    Definition rf : string := instancePrefix--"rf".
    Definition mkRegFileFullModule: Mod := (BKMODULE {
           Register rf : data_t <- Default
           with Method instancePrefix--"sub" (idx : index_t) : data_t :=
             (Read regs : data_t <- rf;
                Ret #regs)
               (* fixme:
             with Method instancePrefix--"upd" (idx : index_t) (v : data_t) : Void :=
               (Read regs : data_t <- rf;
                  Write rf : data_t <- #v;
               Retv)
               *)
    }). (* mkRegFileFull *)

(* Module mkRegFileFull type Module#(RegFile#(index_t, data_t)) return type RegFile#(index_t, data_t) *)
    Definition mkRegFileFull := Build_RegFile mkRegFileFullModule%kami (instancePrefix--"sub") (instancePrefix--"upd").
    End Section'mkRegFileFull.
End module'mkRegFileFull.

Definition mkRegFileFull := module'mkRegFileFull.mkRegFileFull.
Hint Unfold mkRegFileFull : ModuleDefs.
Hint Unfold module'mkRegFileFull.mkRegFileFull : ModuleDefs.
Hint Unfold module'mkRegFileFull.mkRegFileFullModule : ModuleDefs.

(* more stuff *)

Fixpoint toBinaryP (p: positive) : string :=
  match p with
  | xI p' => String "1" (toBinaryP p')
  | xO p' => String "0" (toBinaryP p')
  | xH => ""
  end.

Definition toBinaryN n: string :=
  match n with
  | N0 => "0"
  | Npos p => toBinaryP p
  end.
Check toBinaryN.

Definition toBinaryString (n: nat) := (toBinaryN (N.of_nat n)).

Record ModuleInstance intT :=
    { module : Mod;
      interface : intT;
    }.

Definition bitlt (x y : nat) := (Nat.ltb x y).
Check bitlt.

(* interface for module wrapper for myTruncate *)
Record Interface'myTruncate := {
    Interface'myTruncate'mod: Mod;
    Interface'myTruncate'myTruncate: string;
}.

(* interface for module wrapper for isValid *)
Record Interface'isValid := {
    Interface'isValid'mod: Mod;
    Interface'isValid'isValid: string;
}.
Hint Unfold Interface'isValid'mod : ModuleDefs.
Hint Unfold Interface'isValid'isValid : ModuleDefs.

Module module'isValid.
    Section Section'isValid.
    Variable data_t : Kind.
    Variable instancePrefix: string.
    Local Open Scope kami_expr.
    Definition Modules'isValid: Mod.
        refine (BKMODULE {
        Method1 (instancePrefix--"isValid") (m: (Maybe data_t)) : Bool := 
			  (
			   LET tag : (Bit 1) <- #m @% "$tag";
			   If (#tag == $0) then (
						 Ret ($$true)%kami_expr
						 ) else (
							 Ret ($$false)%kami_expr
							 ) as retval;
			   Ret #retval

			   )
    })%kami; abstract omega. Qed. (* isValid *)
    Definition isValid := Build_Interface'isValid Modules'isValid (instancePrefix--"isValid").
    End Section'isValid.
End module'isValid.

Definition function'isValid := module'isValid.isValid.
Hint Unfold function'isValid : ModuleDefs.
Hint Unfold module'isValid.isValid : ModuleDefs.

(* interface for module wrapper for fromMaybe *)
Record Interface'fromMaybe := {
    Interface'fromMaybe'mod: Mod;
    Interface'fromMaybe'fromMaybe: string;
}.
Hint Unfold Interface'fromMaybe'mod : ModuleDefs.
Hint Unfold Interface'fromMaybe'fromMaybe : ModuleDefs.

Module module'fromMaybe.
    Section Section'fromMaybe.
    Variable data_t : Kind.
    Variable instancePrefix: string.
    Definition paramT := STRUCT_TYPE {"_1" :: data_t; "_2" :: (Maybe data_t) }.
    Local Open Scope kami_expr.

    Definition Modules'fromMaybe: Mod := (BKMODULE {
        Method1 (instancePrefix--"fromMaybe") (param : paramT ) : data_t := 
						    (
						     LET defaultval: data_t <- #param @% "_1" ;
						     LET val: (Maybe data_t) <- #param @% "_2" ;
						     If (#val @% "$tag" == $0) then ( 
										      LET validval <- #val @% "Valid";
										      Ret #validval
										      ) else (
											      Ret #defaultval
											      ) as retval;
						     Ret #retval

						     )
    }). (* fromMaybe *)
    Definition fromMaybe := Build_Interface'fromMaybe Modules'fromMaybe (instancePrefix--"fromMaybe").
    End Section'fromMaybe.
End module'fromMaybe.

Definition function'fromMaybe := module'fromMaybe.fromMaybe.

Hint Unfold function'fromMaybe : ModuleDefs.
Hint Unfold module'fromMaybe.fromMaybe : ModuleDefs.
Hint Unfold module'fromMaybe.Modules'fromMaybe : ModuleDefs.
