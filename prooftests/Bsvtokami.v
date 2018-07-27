Require Import Kami.
Require Import Kami.Lib.Struct.
Require Import Bool Arith String Nat ZArith.

Definition Integer := nat.

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

Notation "$$ v" := (ConstBit v%kami) (at level 0) : bk_scope.
Notation "$$ v" := (ConstBit v%kami) (at level 0) : kami_scope.

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

Notation "'CallM' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ; cont " :=
  (let fields := STRUCT { "_1" :: a1T ; "_2" :: a2T } in
   let args := (STRUCT { "_1" ::= a1; "_2" ::= a2 })%kami_expr in
   (MCall meth%string {| arg := (Struct fields); ret := retT |} args (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0, a1 at level 99, a2 at level 99) : kami_action_scope.

Notation "'Method2' name ( p1 : d1 ) ( p2 : d2 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let fields := STRUCT { "_1" :: d1f ; "_2" :: d2f } in
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := (Struct fields); ret := retT |}
                                   (fun ty => fun param : ty (Struct fields)  =>
                                                 (LET p1 : d1g <-  #param!fields @."_1";
                                                  LET p2 : d2g <-  #param!fields @."_2";
                                                  c)%kami_action : ActionT ty retT)))))
    (at level 0, name at level 0, p1 at level 0, d1 at level 0, p2 at level 0, d2 at level 0).

Notation "'CallM' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T ) ; cont " :=
  (let fields := STRUCT { "_1" :: a1T ; "_2" :: a2T; "_3" :: a3T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 })%kami_expr in
   (MCall meth%string {| arg := (Struct fields); ret := retT |} args (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99) : kami_action_scope.

Notation "'Method3' name ( p1 : d1 ) ( p2 : d2 )  ( p3 : d3 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let d3f := d3 in
   let d3g := d3 in
   let fields := STRUCT { "_1" :: d1f ; "_2" :: d2f; "_3" :: d3f } in
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := (Struct fields); ret := retT |}
                                   (fun ty => fun param : ty (Struct fields)  =>
                                                 (LET p1 : d1g <-  #param!fields @."_1";
                                                  LET p2 : d2g <-  #param!fields @."_2";
                                                  LET p3 : d3g <-  #param!fields @."_3";
                                                  c)%kami_action : ActionT ty retT)))))
    (at level 0, name at level 0, p1 at level 0, d1 at level 0, p2 at level 0, d2 at level 0, p3 at level 0, d3 at level 0).

Notation "'CallM' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T )  ( a4 : a4T ) ; cont " :=
  (let fields := STRUCT { "_1" :: a1T ; "_2" :: a2T; "_3" :: a3T; "_4" :: a4T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 ; "_4" ::= a4 })%kami_expr in
   (MCall meth%string {| arg := (Struct fields); ret := retT |} args (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99, a4 at level 99) : kami_action_scope.

Notation "'Method4' name ( p1 : d1 ) ( p2 : d2 )  ( p3 : d3 ) ( p4 : d4 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let d3f := d3 in
   let d3g := d3 in
   let d4f := d4 in
   let d4g := d4 in
   let fields := STRUCT { "_1" :: d1f ; "_2" :: d2f; "_3" :: d3f; "_4" :: d4f } in
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := (Struct fields); ret := retT |}
                                   (fun ty => fun param : ty (Struct fields)  =>
                                                 (LET p1 : d1g <-  #param!fields @."_1";
                                                  LET p2 : d2g <-  #param!fields @."_2";
                                                  LET p3 : d3g <-  #param!fields @."_3";
                                                  LET p4 : d4g <-  #param!fields @."_4";
                                                  c)%kami_action : ActionT ty retT)))))
    (at level 0, name at level 0, p1 at level 0, d1 at level 0, p2 at level 0, d2 at level 0, p3 at level 0, d3 at level 0, p4 at level 0, d4 at level 0).

Notation "'CallM' name : retT <- meth ( a1 : a1T ) ( a2 : a2T ) ( a3 : a3T ) ( a4 : a4T ) ( a5 : a5T ) ; cont " :=
  (let fields := STRUCT { "_1" :: a1T ; "_2" :: a2T; "_3" :: a3T; "_4" :: a4T; "_5" :: a5T } in
   let args := (STRUCT { "_1" ::= a1 ; "_2" ::= a2 ; "_3" ::= a3 ; "_4" ::= a4 ; "_5" ::= a5 })%kami_expr in
   (MCall meth%string {| arg := (Struct fields); ret := retT |} args (fun name => cont)))
    (at level 12, right associativity, name at level 0, meth at level 0,
     a1 at level 99, a2 at level 99, a3 at level 99, a4 at level 99, a5 at level 99) : kami_action_scope.

Notation "'Method5' name ( p1 : d1 ) ( p2 : d2 )  ( p3 : d3 ) ( p4 : d4 ) ( p5 : d5 ) : retT := c" :=
  (let d1f := d1 in
   let d1g := d1 in
   let d2f := d2 in
   let d2g := d2 in
   let d3f := d3 in
   let d3g := d3 in
   let d4f := d4 in
   let d4g := d4 in
   let d5f := d5 in
   let d5g := d5 in
   let fields := STRUCT { "_1" :: d1f ; "_2" :: d2f; "_3" :: d3f; "_4" :: d4f; "_5" :: d5f } in
  (BKMeth (Build_Attribute name
                           (existT MethodT {| arg := (Struct fields); ret := retT |}
                                   (fun ty => fun param : ty (Struct fields)  =>
                                                 (LET p1 : d1g <-  #param!fields @."_1";
                                                  LET p2 : d2g <-  #param!fields @."_2";
                                                  LET p3 : d3g <-  #param!fields @."_3";
                                                  LET p4 : d4g <-  #param!fields @."_4";
                                                  LET p5 : d5g <-  #param!fields @."_5";
                                                  c)%kami_action : ActionT ty retT)))))
    (at level 0, name at level 0, p1 at level 0, d1 at level 0, p2 at level 0, d2 at level 0, p3 at level 0, d3 at level 0, p4 at level 0, d4 at level 0, p5 at level 0, d5 at level 0).


Definition MaybeFields (a : Kind) := (STRUCT { "$tag" :: (Bit 1); "Invalid" :: (Bit 1); "Valid" :: a }).
Definition Maybe (a : Kind) := (Struct (MaybeFields a)).

Definition castBits ty ni no (pf: ni = no) (e: Expr ty (SyntaxKind (Bit ni))) :=
  match pf in _ = Y return Expr ty (SyntaxKind (Bit Y)) with
    | eq_refl => e
  end.

Record Empty := {
    Empty'modules: Modules;
}.


Definition Tuple2Fields (t1 t2: Kind) := (STRUCT {
    "tpl_1" :: t1;
    "tpl_2" :: t2
}).
Definition Tuple2 (t1 t2: Kind) := Struct (Tuple2Fields t1 t2).

Record Reg := {
    Reg'modules: Modules;
    Reg'_read : string;
    Reg'_write : string;
}.

Module module'mkReg.
    Section Section'mkReg.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable v: ConstT a.
    Definition reg : string := instancePrefix--"reg".
    Definition mkRegModule: Modules :=
      (BKMODULE {
           Register reg : a <- v
           with Method instancePrefix--"_read" () : a :=
             Read v : a <- reg ;
           Ret #v

           with Method instancePrefix--"_write" (v : a) : Void :=
             Write reg : a <- #v;
           Retv

         }). (* mkReg *)

(* Module mkReg type a -> Module#(Reg#(a)) return type Reg#(a) *)
    Definition mkReg := Build_Reg mkRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkReg.
End module'mkReg.

Definition mkReg := module'mkReg.mkReg.

Module module'mkReadOnlyReg.
    Section Section'mkReadOnlyReg.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable v: ConstT a.
    Definition reg : string := instancePrefix--"reg".
    Definition mkReadOnlyRegModule: Modules :=
      (BKMODULE {
           Register reg : a <- v
           with Method instancePrefix--"_read" () : a :=
             Read v : a <- reg ;
           Ret #v

           with Method instancePrefix--"_write" (v : a) : Void :=
             Retv

         }). (* mkReadOnlyReg *)

(* Module mkReadOnlyReg type a -> Module#(Reg#(a)) return type Reg#(a) *)
    Definition mkReadOnlyReg := Build_Reg mkReadOnlyRegModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkReadOnlyReg.
End module'mkReadOnlyReg.

Definition mkReadOnlyReg := module'mkReadOnlyReg.mkReadOnlyReg.

(* mkRegU *)
Module module'mkRegU.
    Section Section'mkRegU.
    Variable a : Kind.
    Variable instancePrefix: string.
    Variable v: ConstT a.
    Definition reg : string := instancePrefix--"reg".
    Definition mkRegUModule: Modules :=
        (BKMODULE {
           Register reg : a <- Default
           with Method instancePrefix--"_read" () : a :=
             Read v : a <- reg ;
             Ret #v

           with Method instancePrefix--"_write" (v : a) : Void :=
             Write reg : a <- #v;
             Retv

           }). (* mkRegU *)

(* Module mkRegU type a -> Module#(Reg#(a)) return type Reg#(a) *)
    Definition mkRegU := Build_Reg mkRegUModule%kami (instancePrefix--"_read") (instancePrefix--"_write").
    End Section'mkRegU.
End module'mkRegU.

Definition mkRegU := module'mkRegU.mkRegU.

(* more stuff *)

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
    { module : Modules;
      interface : intT;
    }.

Definition bitlt (x : nat) (y: nat): bool := (Nat.ltb x y).

