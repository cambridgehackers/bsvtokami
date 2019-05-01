Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.

Require Import FunctionalExtensionality.

Set Implicit Arguments.


Require Import DefaultValue.
Require Import RegFile.
Definition DataSz := 32.

Definition AddrSz := 32.

Definition InstrSz := 32.

Definition NumRegs := 32.

Definition RegFileSz := Nat.log2 NumRegs.

Definition NumInstrs := 8.

Definition PgmSz := Nat.log2 NumInstrs.

Definition opArith : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 0))%kami.

Definition opLd : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 1))%kami.

Definition opSt : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 2))%kami.

Definition opTh : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 3))%kami.

Definition OpK := Bit 2.

Definition opArithAdd : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 0))%kami.

Definition opArithSub : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 1))%kami.

Definition opArithMul : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 2))%kami.

Definition opArithDiv : ConstT (Bit 2) := ( (* intwidth *) (natToWord 2 3))%kami.

Definition OpArithK := Bit 2.

(* * interface Decoder *)
Record Decoder := {
    Decoder'mod: Mod;
    Decoder'isOp : string;
    Decoder'getOp : string;
    Decoder'getArithOp : string;
    Decoder'getSrc1 : string;
    Decoder'getSrc2 : string;
    Decoder'getDst : string;
    Decoder'getAddr : string;
}.

Hint Unfold Decoder'mod : ModuleDefs.
Hint Unfold Decoder'isOp : ModuleDefs.
Hint Unfold Decoder'getOp : ModuleDefs.
Hint Unfold Decoder'getArithOp : ModuleDefs.
Hint Unfold Decoder'getSrc1 : ModuleDefs.
Hint Unfold Decoder'getSrc2 : ModuleDefs.
Hint Unfold Decoder'getDst : ModuleDefs.
Hint Unfold Decoder'getAddr : ModuleDefs.

(* * interface Executer *)
Record Executer := {
    Executer'mod: Mod;
    Executer'execArith : string;
}.

Hint Unfold Executer'mod : ModuleDefs.
Hint Unfold Executer'execArith : ModuleDefs.

Definition MemRq := (STRUCT {
    "addr" :: Bit AddrSz;
    "data" :: Bit DataSz;
    "isLoad" :: Bit 1}).


(* * interface ToHost *)
Record ToHost := {
    ToHost'mod: Mod;
    ToHost'toHost : string;
}.

Hint Unfold ToHost'mod : ModuleDefs.
Hint Unfold ToHost'toHost : ModuleDefs.


