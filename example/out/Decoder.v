Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.
Require Import ProcMemSpec.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Record Decoder :=
  { getOp: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind OpK) ;
    getArithOp: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind OpArithK) ;
    getSrc1: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
    getSrc2: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
    getDst: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
    getAddr: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit AddrSz))
  }.

Definition decStub := Build_Decoder
			  (fun ty (instr: ty (Bit InstrSz)) => ($$opLd)%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$opArithAdd)%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord RegFileSz 0))%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord RegFileSz 0))%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord RegFileSz 0))%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord AddrSz 0))%kami_expr)
			  .

Record Executer :=
  {
    execArith: forall ty, ty OpArithK -> ty (Bit DataSz) -> ty (Bit DataSz) -> Expr ty (SyntaxKind (Bit DataSz))
  }.

Definition execStub := Build_Executer
			  (fun ty (op: ty OpArithK) (val1 val2: ty (Bit DataSz)) => ($$(natToWord DataSz 22))%kami_expr).

Module module'decoder.
    Section Section'decoder.
    Variable dec : Decoder.
    Variable instancePrefix: string.
    Definition paramT := STRUCT {"_1" :: (Bit InstrSz)%kami_expr; "_2" :: OpK }%kami.
    Local Open Scope kami_expr.
    Definition decoderModule: Mod :=
         (BKMODULE {
              Method (instancePrefix--"getOp") ( instr : Bit InstrSz ) : OpK :=
                (
                  LET instr_v : Bit InstrSz <- (Var _ (SyntaxKind _) instr) ;
                    Ret (getOp dec _ instr_v)
                )
              with Method (instancePrefix--"isOp") ( param : paramT ) : Bool :=
                (
                  LET instr_v : Bit InstrSz <- #param @% "_1" ;
                  LET op1 : OpK <- #param @% "_2" ;
                    LET op2 : OpK <- (getOp dec _ instr_v) ;
                    Ret (#op1 == #op2)
                )
              with Method (instancePrefix--"getArithOp") ( instr : Bit InstrSz ) : OpArithK :=
                (
                  LET instr_v : Bit InstrSz <- (Var _ (SyntaxKind _) instr) ;
                    Ret (getArithOp dec _ instr_v)
                )
              with Method (instancePrefix--"getSrc1") ( instr : Bit InstrSz ) : (Bit RegFileSz) :=
                (
                  LET instr_v : Bit InstrSz <- (Var _ (SyntaxKind _) instr) ;
                    Ret (getSrc1 dec _ instr_v)
                )
              with Method (instancePrefix--"getSrc2") ( instr : Bit InstrSz ) : (Bit RegFileSz) :=
                (
                  LET instr_v : Bit InstrSz <-
                                    (Var _ (SyntaxKind _) instr) ;
                    Ret (getSrc2 dec _ instr_v)
                )
              with Method (instancePrefix--"getDst") ( instr : Bit InstrSz ) : (Bit RegFileSz) :=
                (
                  LET instr_v : Bit InstrSz <-
                                    (Var _ (SyntaxKind _) instr) ;
                    Ret (getDst dec _ instr_v)
                )
              with Method (instancePrefix--"getAddr") ( instr : Bit InstrSz ) : (Bit AddrSz) :=
                (
                  LET instr_v : Bit InstrSz <-
                                    (Var _ (SyntaxKind _) instr) ;
                    Ret (getAddr dec _ instr_v)
                )
         }).
    Definition mkDecoder := ProcMemSpec.Build_Decoder
                              decoderModule
                              (instancePrefix--"isOp")
                              (instancePrefix--"getOp")
                              (instancePrefix--"getArithOp")
                              (instancePrefix--"getSrc1")
                              (instancePrefix--"getSrc2")
                              (instancePrefix--"getDst")
                              (instancePrefix--"getAddr").
    End Section'decoder.
End module'decoder.

Definition mkDecoder := module'decoder.mkDecoder.
Hint Unfold module'decoder.decoderModule : ModuleDefs.
Hint Unfold module'decoder.mkDecoder.
Hint Unfold mkDecoder.
Check mkDecoder.

Module module'executer.
    Section Section'executer.
    Variable exec : Executer.
    Variable instancePrefix: string.
    Definition paramT := STRUCT {
                             "_1" :: OpArithK ;
                             "_2" :: (Bit DataSz) ;
                             "_3" :: (Bit DataSz)}%kami.
    Local Open Scope kami_expr.
    Definition executerModule: Mod :=
         (BKMODULE {
              Method (instancePrefix--"execArith") ( param : paramT ) : (Bit DataSz) :=
                (
                  LET op : OpArithK <- #param @% "_1" ;
                  LET val1 : Bit DataSz <- #param @% "_2" ;
                  LET val2 : Bit DataSz <- #param @% "_3" ;
                  LET val : Bit DataSz <- (execArith exec _ op val1 val2) ;
                  Ret #val
                )
         }).
    Definition mkExecuter := ProcMemSpec.Build_Executer
                              executerModule
                              (instancePrefix--"execArith").
    End Section'executer.
End module'executer.

Definition mkExecuter := module'executer.mkExecuter.
Hint Unfold module'executer.executerModule : ModuleDefs.
Hint Unfold module'executer.mkExecuter.
Hint Unfold mkExecuter.
Check mkExecuter.
