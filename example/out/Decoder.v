Require Import Bool String List Arith.
Require Import Omega.
Require Import Kami.All.
Require Import Bsvtokami.
Require Import ProcMemSpec.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Record Decoder :=
  { getOp: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit 2)) ;
    getArithOp: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit 2)) ;
    getSrc1: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
    getSrc2: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
    getDst: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit RegFileSz)) ;
    getAddr: forall ty, ty (Bit InstrSz) -> Expr ty (SyntaxKind (Bit AddrSz))
  }.

Hint Unfold Decoder'getAddr : ModuleDefs.
Hint Unfold Decoder'getOp : ModuleDefs.
Hint Unfold Decoder'getArithOp : ModuleDefs.
Hint Unfold Decoder'getDst : ModuleDefs.
Hint Unfold Decoder'getSrc1 : ModuleDefs.
Hint Unfold Decoder'getSrc2 : ModuleDefs.

Definition decStub := Build_Decoder
			  (fun ty (instr: ty (Bit InstrSz)) => ($$opLd)%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$opArithAdd)%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord RegFileSz 0))%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord RegFileSz 0))%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord RegFileSz 0))%kami_expr)
			  (fun ty (instr: ty (Bit InstrSz)) => ($$(natToWord AddrSz 0))%kami_expr)
			  .

Definition ExecuterResult := STRUCT_TYPE { "data" :: Bit DataSz ; "addr" :: Bit AddrSz ; "nextpc" :: Bit PgmSz }.

Record Executer :=
  {
    execArith: forall ty, ty (Bit 2) -> ty (Bit DataSz) -> ty (Bit DataSz) -> Expr ty (SyntaxKind ExecuterResult )
  }.

Hint Unfold Executer'execArith : ModuleDefs.

Module module'decoder.
    Section Section'decoder.
    Variable dec : Decoder.
    Variable instancePrefix: string.
    Definition paramT := STRUCT_TYPE {"_1" :: (Bit InstrSz)%kami_expr; "_2" :: OpK }%kami.
    Local Open Scope kami_expr.
    Definition decoderModule: ModWf :=
         (MOD_WF {
              Method (instancePrefix--"getOp") ( instr : Bit InstrSz ) : OpK :=
                (
                  LET instr_v : Bit InstrSz <- (Var _ (SyntaxKind _) instr) ;
                    Ret (getOp dec _ instr_v)
                )
              with Method (instancePrefix--"getArithOp") ( instr : Bit InstrSz ) : Bit 2 :=
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
Hint Unfold module'decoder.mkDecoder : ModuleDefs.
Hint Unfold module'decoder.paramT : ModuleDefs.
Hint Unfold mkDecoder : ModuleDefs.
Check mkDecoder.

Module module'executer.
    Section Section'executer.
    Variable exec : Executer.
    Variable instancePrefix: string.
    Definition paramT := STRUCT_TYPE {
                             "_1" :: Bit 2 ;
                             "_2" :: (Bit DataSz) ;
                             "_3" :: (Bit DataSz)}%kami.
    Local Open Scope kami_expr.
    Definition executerModule: ModWf :=
         (MOD_WF {
              Method (instancePrefix--"execArith") ( param : paramT ) : ExecuterResult :=
                (
                  LET op : Bit 2 <- #param @% "_1" ;
                  LET val1 : Bit DataSz <- #param @% "_2" ;
                  LET val2 : Bit DataSz <- #param @% "_3" ;
                  LET val : ExecuterResult <- (execArith exec _ op val1 val2) ;
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
Hint Unfold module'executer.mkExecuter : ModuleDefs.
Hint Unfold module'executer.paramT : ModuleDefs.
Hint Unfold mkExecuter : ModuleDefs.
Check mkExecuter.
