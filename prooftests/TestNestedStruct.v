Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.
Require Import Lib.Indexer.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

(* Bsvtokami.v *)

Require Import Kami.Lib.Struct.
Require Import Nat ZArith.

Record Empty := {
    Empty'modules: Modules;
}.

Record Reg (a : Kind) := {
    Reg'modules: Modules;
    Reg'_read : string;
    Reg'_write : string;
}.

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

(* end of Bsvtokami.v *)

Definition XLEN := 32.

Definition DataSz := XLEN.

Definition Data := (Bit 32).

Definition CacheLineSz := 512.

Definition InstSz := 32.

Definition Instruction := (Bit InstSz).

Definition AddrSz := XLEN.

Definition PAddrSz := 64.

Definition AsidSz := 10.

Definition Asid := (Bit AsidSz).

Definition RVRoundModeFields := (STRUCT { "$tag" :: (Bit 3) }).
Definition RVRoundMode := (Struct RVRoundModeFields).
Notation RNE := (STRUCT { "$tag" ::= $$(natToWord 3 0) })%kami_expr.
Notation RTZ := (STRUCT { "$tag" ::= $$(natToWord 3 1) })%kami_expr.
Notation RDN := (STRUCT { "$tag" ::= $$(natToWord 3 2) })%kami_expr.
Notation RUP := (STRUCT { "$tag" ::= $$(natToWord 3 3) })%kami_expr.
Notation RMM := (STRUCT { "$tag" ::= $$(natToWord 3 4) })%kami_expr.
Notation RDyn := (STRUCT { "$tag" ::= $$(natToWord 3 5) })%kami_expr.
(* * interface Pack#(t, sz) *)
Record Pack (t : Kind) (sz : nat) := {
    Pack'modules: Modules;
    Pack'unpack : string;
    Pack'pack : string;
}.

Module module'mkPackRVRoundMode.
    Section Section'mkPackRVRoundMode.
    Variable instancePrefix: string.
            Definition mkPackRVRoundModeModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 3)) : RVRoundMode :=
    If (#v == $0) then (
        Ret RNE

   ) else (
    If (#v == $1) then (
        Ret RTZ

   ) else (
    If (#v == $2) then (
        Ret RDN

   ) else (
    If (#v == $3) then (
        Ret RUP

   ) else (
    If (#v == $4) then (
        Ret RMM

   ) else (
    If (#v == $7) then (
        Ret RDyn

   ) else (
        Ret RDyn
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


       with Method instancePrefix--"pack" (v : RVRoundMode) : (Bit 3) :=
    If (#v!RVRoundModeFields@."$tag" == $0) then (
        Ret $0

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $1) then (
        Ret $1

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $2) then (
        Ret $2

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $3) then (
        Ret $3

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $4) then (
        Ret $4

   ) else (
    If (#v!RVRoundModeFields@."$tag" == $7) then (
        Ret $7

   ) else (
        Ret $7
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


    }). (* mkPackRVRoundMode *)

(* Module mkPackRVRoundMode type Module#(Pack#(RVRoundMode, 3)) return type Pack#(RVRoundMode, 3) *)
    Definition mkPackRVRoundMode := Build_Pack (RVRoundMode) (3) mkPackRVRoundModeModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackRVRoundMode.
End module'mkPackRVRoundMode.

Definition mkPackRVRoundMode := module'mkPackRVRoundMode.mkPackRVRoundMode.

Definition OpcodeFields := (STRUCT { "$tag" :: (Bit 5) }).
Definition Opcode := (Struct OpcodeFields).
Notation Load := (STRUCT { "$tag" ::= $$(natToWord 5 0) })%kami_expr.
Notation LoadFp := (STRUCT { "$tag" ::= $$(natToWord 5 1) })%kami_expr.
Notation MiscMem := (STRUCT { "$tag" ::= $$(natToWord 5 2) })%kami_expr.
Notation OpImm := (STRUCT { "$tag" ::= $$(natToWord 5 3) })%kami_expr.
Notation Auipc := (STRUCT { "$tag" ::= $$(natToWord 5 4) })%kami_expr.
Notation OpImm32 := (STRUCT { "$tag" ::= $$(natToWord 5 5) })%kami_expr.
Notation Store := (STRUCT { "$tag" ::= $$(natToWord 5 6) })%kami_expr.
Notation StoreFp := (STRUCT { "$tag" ::= $$(natToWord 5 7) })%kami_expr.
Notation Amo := (STRUCT { "$tag" ::= $$(natToWord 5 8) })%kami_expr.
Notation Op := (STRUCT { "$tag" ::= $$(natToWord 5 9) })%kami_expr.
Notation Lui := (STRUCT { "$tag" ::= $$(natToWord 5 10) })%kami_expr.
Notation Op32 := (STRUCT { "$tag" ::= $$(natToWord 5 11) })%kami_expr.
Notation Fmadd := (STRUCT { "$tag" ::= $$(natToWord 5 12) })%kami_expr.
Notation Fmsub := (STRUCT { "$tag" ::= $$(natToWord 5 13) })%kami_expr.
Notation Fnmsub := (STRUCT { "$tag" ::= $$(natToWord 5 14) })%kami_expr.
Notation Fnmadd := (STRUCT { "$tag" ::= $$(natToWord 5 15) })%kami_expr.
Notation OpFp := (STRUCT { "$tag" ::= $$(natToWord 5 16) })%kami_expr.
Notation Branch := (STRUCT { "$tag" ::= $$(natToWord 5 17) })%kami_expr.
Notation Jalr := (STRUCT { "$tag" ::= $$(natToWord 5 18) })%kami_expr.
Notation Jal := (STRUCT { "$tag" ::= $$(natToWord 5 19) })%kami_expr.
Notation System := (STRUCT { "$tag" ::= $$(natToWord 5 20) })%kami_expr.
Module module'mkPackOpcode.
    Section Section'mkPackOpcode.
    Variable instancePrefix: string.
            Definition mkPackOpcodeModule: Modules :=
         (BKMODULE {
           Method instancePrefix--"unpack" (v : (Bit 7)) : Opcode :=
    If (#v == $3) then (
        Ret Load

   ) else (
    If (#v == $7) then (
        Ret LoadFp

   ) else (
    If (#v == $15) then (
        Ret MiscMem

   ) else (
    If (#v == $19) then (
        Ret OpImm

   ) else (
    If (#v == $23) then (
        Ret Auipc

   ) else (
    If (#v == $27) then (
        Ret OpImm32

   ) else (
    If (#v == $35) then (
        Ret Store

   ) else (
    If (#v == $39) then (
        Ret StoreFp

   ) else (
    If (#v == $47) then (
        Ret Amo

   ) else (
    If (#v == $51) then (
        Ret Op

   ) else (
    If (#v == $55) then (
        Ret Lui

   ) else (
    If (#v == $59) then (
        Ret Op32

   ) else (
    If (#v == $67) then (
        Ret Fmadd

   ) else (
    If (#v == $71) then (
        Ret Fmsub

   ) else (
    If (#v == $75) then (
        Ret Fnmsub

   ) else (
    If (#v == $79) then (
        Ret Fnmadd

   ) else (
    If (#v == $83) then (
        Ret OpFp

   ) else (
    If (#v == $99) then (
        Ret Branch

   ) else (
    If (#v == $103) then (
        Ret Jalr

   ) else (
    If (#v == $111) then (
        Ret Jal

   ) else (
    If (#v == $115) then (
        Ret System

   ) else (
        Ret System
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


       with Method instancePrefix--"pack" (v : Opcode) : (Bit 7) :=
    If (#v!OpcodeFields@."$tag" == $3) then (
        Ret $3

   ) else (
    If (#v!OpcodeFields@."$tag" == $7) then (
        Ret $7

   ) else (
    If (#v!OpcodeFields@."$tag" == $15) then (
        Ret $15

   ) else (
    If (#v!OpcodeFields@."$tag" == $19) then (
        Ret $19

   ) else (
    If (#v!OpcodeFields@."$tag" == $23) then (
        Ret $23

   ) else (
    If (#v!OpcodeFields@."$tag" == $27) then (
        Ret $27

   ) else (
    If (#v!OpcodeFields@."$tag" == $35) then (
        Ret $35

   ) else (
    If (#v!OpcodeFields@."$tag" == $39) then (
        Ret $39

   ) else (
    If (#v!OpcodeFields@."$tag" == $47) then (
        Ret $47

   ) else (
    If (#v!OpcodeFields@."$tag" == $51) then (
        Ret $51

   ) else (
    If (#v!OpcodeFields@."$tag" == $55) then (
        Ret $55

   ) else (
    If (#v!OpcodeFields@."$tag" == $59) then (
        Ret $59

   ) else (
    If (#v!OpcodeFields@."$tag" == $67) then (
        Ret $67

   ) else (
    If (#v!OpcodeFields@."$tag" == $71) then (
        Ret $71

   ) else (
    If (#v!OpcodeFields@."$tag" == $75) then (
        Ret $75

   ) else (
    If (#v!OpcodeFields@."$tag" == $79) then (
        Ret $79

   ) else (
    If (#v!OpcodeFields@."$tag" == $83) then (
        Ret $83

   ) else (
    If (#v!OpcodeFields@."$tag" == $99) then (
        Ret $99

   ) else (
    If (#v!OpcodeFields@."$tag" == $103) then (
        Ret $103

   ) else (
    If (#v!OpcodeFields@."$tag" == $111) then (
        Ret $111

   ) else (
    If (#v!OpcodeFields@."$tag" == $115) then (
        Ret $115

   ) else (
        Ret $0
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval
) as retval; Ret #retval


    }). (* mkPackOpcode *)

(* Module mkPackOpcode type Module#(Pack#(Opcode, 7)) return type Pack#(Opcode, 7) *)
    Definition mkPackOpcode := Build_Pack (Opcode) (7) mkPackOpcodeModule%kami (instancePrefix--"pack") (instancePrefix--"unpack").
    End Section'mkPackOpcode.
End module'mkPackOpcode.

Definition mkPackOpcode := module'mkPackOpcode.mkPackOpcode.


Definition InstructionFieldsFields := (STRUCT {
    "inst" :: (Bit 32);
    "rd" :: (Bit 5);
    "rs1" :: (Bit 5);
    "rs2" :: (Bit 5);
    "rs3" :: (Bit 5);
    "funct2" :: (Bit 2);
    "funct3" :: (Bit 3);
    "funct5" :: (Bit 5);
    "funct7" :: (Bit 7);
    "fmt" :: (Bit 2);
    "rm" :: RVRoundMode;
    "csrAddr" :: (Bit 12)}).
Definition InstructionFields  := Struct (InstructionFieldsFields).

Definition TestStructFields := (STRUCT {
    "inst" :: (Bit 32);
    "rd" :: (Bit 5)}).
Definition TestStruct  := Struct (TestStructFields).

(* * interface GetTestStruct *)
Record GetTestStruct := {
    GetTestStruct'modules: Modules;
    GetTestStruct'getTestStruct : string;
}.

Module module'mkTestStruct.
    Section Section'mkTestStruct.
    Variable instancePrefix: string.
    Definition mkTestStructModule: Modules :=
         (BKMODULE {
              Method instancePrefix--"getTestStruct" (x : (Bit 32)) : TestStruct :=
        LET ts : TestStruct <- STRUCT { "inst" ::= (#x); "rd" ::= (#x$[4:0]@32)  };
        Ret #ts

    }). (* mkTestStruct *)

(* Module mkTestStruct type Module#(GetTestStruct) return type GetTestStruct *)
    Definition mkTestStruct := Build_GetTestStruct mkTestStructModule%kami (instancePrefix--"getTestStruct").
    End Section'mkTestStruct.
End module'mkTestStruct.

Definition mkTestStruct := module'mkTestStruct.mkTestStruct.

(* * interface GetInstFields *)
Record GetInstFields := {
    GetInstFields'modules: Modules;
    GetInstFields'getInstFields : string;
}.

Module module'mkGetInstFields.
  Section Section'mkGetInstFields.
    Variable instancePrefix: string.
    Let packRVRoundMode := mkPackRVRoundMode (instancePrefix--"packRVRoundMode").
    Let packOpcode := mkPackOpcode (instancePrefix--"packOpcode").
    Let packOpcodeunpack := MethodSig (Pack'unpack packOpcode) (Bit 7) : Opcode.
    Let packRVRoundModeunpack := MethodSig (Pack'unpack packRVRoundMode) (Bit 3) : RVRoundMode.
    Definition mkGetInstFieldsModule: Modules :=
      (MODULE {
           Method instancePrefix--"getInstFields" (x : Instruction) : InstructionFields :=
           Call xopcode : Opcode <-  packOpcodeunpack(#x$[6:0]@32);
             Call xroundMode : RVRoundMode <-  packRVRoundModeunpack(#x$[14:12]@32);
           LET instFields : InstructionFields <- STRUCT { "inst" ::= (#x); "rd" ::= (#x$[11:7]@32); "rs1" ::= (#x$[19:15]@32); "rs2" ::= (#x$[24:20]@32); "rs3" ::= (#x$[31:27]@32); "funct2" ::= (#x$[26:25]@32); "funct3" ::= (#x$[14:12]@32); "funct5" ::= (#x$[31:27]@32); "funct7" ::= (#x$[31:25]@32); "fmt" ::= (#x$[26:25]@32); "rm" ::= (#xroundMode); "csrAddr" ::= (#x$[31:20]@32)  };
           Ret #instFields

         }). (* mkGetInstFields *)

(* Module mkGetInstFields type Module#(GetInstFields) return type GetInstFields *)
    Definition mkGetInstFields := Build_GetInstFields mkGetInstFieldsModule%kami (instancePrefix--"getInstFields").
    End Section'mkGetInstFields.
End module'mkGetInstFields.

Definition mkGetInstFields := module'mkGetInstFields.mkGetInstFields.

Print mkGetInstFields.
