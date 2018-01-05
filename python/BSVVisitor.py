# Generated from BSV.g4 by ANTLR 4.7.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .BSVParser import BSVParser
else:
    from BSVParser import BSVParser

# This class defines a complete generic visitor for a parse tree produced by BSVParser.

class BSVVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by BSVParser#packagedef.
    def visitPackagedef(self, ctx:BSVParser.PackagedefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#packagedecl.
    def visitPackagedecl(self, ctx:BSVParser.PackagedeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#endpackage.
    def visitEndpackage(self, ctx:BSVParser.EndpackageContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#lowerCaseIdentifier.
    def visitLowerCaseIdentifier(self, ctx:BSVParser.LowerCaseIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#upperCaseIdentifier.
    def visitUpperCaseIdentifier(self, ctx:BSVParser.UpperCaseIdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#identifier.
    def visitIdentifier(self, ctx:BSVParser.IdentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#anyidentifier.
    def visitAnyidentifier(self, ctx:BSVParser.AnyidentifierContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#exportdecl.
    def visitExportdecl(self, ctx:BSVParser.ExportdeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#exportitem.
    def visitExportitem(self, ctx:BSVParser.ExportitemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#importdecl.
    def visitImportdecl(self, ctx:BSVParser.ImportdeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#importitem.
    def visitImportitem(self, ctx:BSVParser.ImportitemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#packagestmt.
    def visitPackagestmt(self, ctx:BSVParser.PackagestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#interfacedecl.
    def visitInterfacedecl(self, ctx:BSVParser.InterfacedeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#interfacememberdecl.
    def visitInterfacememberdecl(self, ctx:BSVParser.InterfacememberdeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#methodproto.
    def visitMethodproto(self, ctx:BSVParser.MethodprotoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#methodprotoformals.
    def visitMethodprotoformals(self, ctx:BSVParser.MethodprotoformalsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#methodprotoformal.
    def visitMethodprotoformal(self, ctx:BSVParser.MethodprotoformalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#subinterfacedecl.
    def visitSubinterfacedecl(self, ctx:BSVParser.SubinterfacedeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedecl.
    def visitTypedecl(self, ctx:BSVParser.TypedeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedeftype.
    def visitTypedeftype(self, ctx:BSVParser.TypedeftypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeformals.
    def visitTypeformals(self, ctx:BSVParser.TypeformalsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeformal.
    def visitTypeformal(self, ctx:BSVParser.TypeformalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedefsynonym.
    def visitTypedefsynonym(self, ctx:BSVParser.TypedefsynonymContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedefenum.
    def visitTypedefenum(self, ctx:BSVParser.TypedefenumContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedefenumelement.
    def visitTypedefenumelement(self, ctx:BSVParser.TypedefenumelementContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedefstruct.
    def visitTypedefstruct(self, ctx:BSVParser.TypedefstructContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedeftaggedunion.
    def visitTypedeftaggedunion(self, ctx:BSVParser.TypedeftaggedunionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#structmember.
    def visitStructmember(self, ctx:BSVParser.StructmemberContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#unionmember.
    def visitUnionmember(self, ctx:BSVParser.UnionmemberContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#substruct.
    def visitSubstruct(self, ctx:BSVParser.SubstructContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#subunion.
    def visitSubunion(self, ctx:BSVParser.SubunionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#derives.
    def visitDerives(self, ctx:BSVParser.DerivesContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#VarBinding.
    def visitVarBinding(self, ctx:BSVParser.VarBindingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#ActionBinding.
    def visitActionBinding(self, ctx:BSVParser.ActionBindingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#LetBinding.
    def visitLetBinding(self, ctx:BSVParser.LetBindingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#PatternBinding.
    def visitPatternBinding(self, ctx:BSVParser.PatternBindingContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#varinit.
    def visitVarinit(self, ctx:BSVParser.VarinitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#arraydims.
    def visitArraydims(self, ctx:BSVParser.ArraydimsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeclassdecl.
    def visitTypeclassdecl(self, ctx:BSVParser.TypeclassdeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeclasside.
    def visitTypeclasside(self, ctx:BSVParser.TypeclassideContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedepends.
    def visitTypedepends(self, ctx:BSVParser.TypedependsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typedepend.
    def visitTypedepend(self, ctx:BSVParser.TypedependContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typelist.
    def visitTypelist(self, ctx:BSVParser.TypelistContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#overloadeddef.
    def visitOverloadeddef(self, ctx:BSVParser.OverloadeddefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#tctype.
    def visitTctype(self, ctx:BSVParser.TctypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeclassinstance.
    def visitTypeclassinstance(self, ctx:BSVParser.TypeclassinstanceContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduledef.
    def visitModuledef(self, ctx:BSVParser.ModuledefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleproto.
    def visitModuleproto(self, ctx:BSVParser.ModuleprotoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleformalparams.
    def visitModuleformalparams(self, ctx:BSVParser.ModuleformalparamsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleformalparam.
    def visitModuleformalparam(self, ctx:BSVParser.ModuleformalparamContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleformalargs.
    def visitModuleformalargs(self, ctx:BSVParser.ModuleformalargsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#modulestmt.
    def visitModulestmt(self, ctx:BSVParser.ModulestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleinst.
    def visitModuleinst(self, ctx:BSVParser.ModuleinstContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleapp.
    def visitModuleapp(self, ctx:BSVParser.ModuleappContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#moduleactualparamarg.
    def visitModuleactualparamarg(self, ctx:BSVParser.ModuleactualparamargContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#methoddef.
    def visitMethoddef(self, ctx:BSVParser.MethoddefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#methodformals.
    def visitMethodformals(self, ctx:BSVParser.MethodformalsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#methodformal.
    def visitMethodformal(self, ctx:BSVParser.MethodformalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#implicitcond.
    def visitImplicitcond(self, ctx:BSVParser.ImplicitcondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#subinterfacedef.
    def visitSubinterfacedef(self, ctx:BSVParser.SubinterfacedefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#ruledef.
    def visitRuledef(self, ctx:BSVParser.RuledefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#rulecond.
    def visitRulecond(self, ctx:BSVParser.RulecondContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#rulebody.
    def visitRulebody(self, ctx:BSVParser.RulebodyContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#functiondef.
    def visitFunctiondef(self, ctx:BSVParser.FunctiondefContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#functionproto.
    def visitFunctionproto(self, ctx:BSVParser.FunctionprotoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#functionformals.
    def visitFunctionformals(self, ctx:BSVParser.FunctionformalsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#functionformal.
    def visitFunctionformal(self, ctx:BSVParser.FunctionformalContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#externcimport.
    def visitExterncimport(self, ctx:BSVParser.ExterncimportContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bigcfuncargs.
    def visitBigcfuncargs(self, ctx:BSVParser.BigcfuncargsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bigcfuncarg.
    def visitBigcfuncarg(self, ctx:BSVParser.BigcfuncargContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#varassign.
    def visitVarassign(self, ctx:BSVParser.VarassignContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#lvalue.
    def visitLvalue(self, ctx:BSVParser.LvalueContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bsvtype.
    def visitBsvtype(self, ctx:BSVParser.BsvtypeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeprimary.
    def visitTypeprimary(self, ctx:BSVParser.TypeprimaryContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeide.
    def visitTypeide(self, ctx:BSVParser.TypeideContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typenat.
    def visitTypenat(self, ctx:BSVParser.TypenatContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#OperatorExpr.
    def visitOperatorExpr(self, ctx:BSVParser.OperatorExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#MatchesExpr.
    def visitMatchesExpr(self, ctx:BSVParser.MatchesExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#SimpleCondExpr.
    def visitSimpleCondExpr(self, ctx:BSVParser.SimpleCondExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#CaseExpr.
    def visitCaseExpr(self, ctx:BSVParser.CaseExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#CondExpr.
    def visitCondExpr(self, ctx:BSVParser.CondExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#caseexpritem.
    def visitCaseexpritem(self, ctx:BSVParser.CaseexpritemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#caseexprdefaultitem.
    def visitCaseexprdefaultitem(self, ctx:BSVParser.CaseexprdefaultitemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#binopexpr.
    def visitBinopexpr(self, ctx:BSVParser.BinopexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#unopexpr.
    def visitUnopexpr(self, ctx:BSVParser.UnopexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bitconcat.
    def visitBitconcat(self, ctx:BSVParser.BitconcatContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#varexpr.
    def visitVarexpr(self, ctx:BSVParser.VarexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#blockexpr.
    def visitBlockexpr(self, ctx:BSVParser.BlockexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#structexpr.
    def visitStructexpr(self, ctx:BSVParser.StructexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#stringliteral.
    def visitStringliteral(self, ctx:BSVParser.StringliteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#rulesexpr.
    def visitRulesexpr(self, ctx:BSVParser.RulesexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#intliteral.
    def visitIntliteral(self, ctx:BSVParser.IntliteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#realliteral.
    def visitRealliteral(self, ctx:BSVParser.RealliteralContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#castexpr.
    def visitCastexpr(self, ctx:BSVParser.CastexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#resetbyexpr.
    def visitResetbyexpr(self, ctx:BSVParser.ResetbyexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#undefinedexpr.
    def visitUndefinedexpr(self, ctx:BSVParser.UndefinedexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#clockedbyexpr.
    def visitClockedbyexpr(self, ctx:BSVParser.ClockedbyexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#returnexpr.
    def visitReturnexpr(self, ctx:BSVParser.ReturnexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#fieldexpr.
    def visitFieldexpr(self, ctx:BSVParser.FieldexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#parenexpr.
    def visitParenexpr(self, ctx:BSVParser.ParenexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#interfaceexpr.
    def visitInterfaceexpr(self, ctx:BSVParser.InterfaceexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#actionblockexpr.
    def visitActionblockexpr(self, ctx:BSVParser.ActionblockexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#parfsmstmtexpr.
    def visitParfsmstmtexpr(self, ctx:BSVParser.ParfsmstmtexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#callexpr.
    def visitCallexpr(self, ctx:BSVParser.CallexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#valueofexpr.
    def visitValueofexpr(self, ctx:BSVParser.ValueofexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#seqfsmstmtexpr.
    def visitSeqfsmstmtexpr(self, ctx:BSVParser.SeqfsmstmtexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#taggedunionexpr.
    def visitTaggedunionexpr(self, ctx:BSVParser.TaggedunionexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#arraysub.
    def visitArraysub(self, ctx:BSVParser.ArraysubContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#actionvalueblockexpr.
    def visitActionvalueblockexpr(self, ctx:BSVParser.ActionvalueblockexprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#typeassertion.
    def visitTypeassertion(self, ctx:BSVParser.TypeassertionContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#memberbinds.
    def visitMemberbinds(self, ctx:BSVParser.MemberbindsContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#memberbind.
    def visitMemberbind(self, ctx:BSVParser.MemberbindContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#interfacestmt.
    def visitInterfacestmt(self, ctx:BSVParser.InterfacestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#rulesstmt.
    def visitRulesstmt(self, ctx:BSVParser.RulesstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#beginendblock.
    def visitBeginendblock(self, ctx:BSVParser.BeginendblockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#actionblock.
    def visitActionblock(self, ctx:BSVParser.ActionblockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#actionvalueblock.
    def visitActionvalueblock(self, ctx:BSVParser.ActionvalueblockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#regwrite.
    def visitRegwrite(self, ctx:BSVParser.RegwriteContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#stmt.
    def visitStmt(self, ctx:BSVParser.StmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#ifstmt.
    def visitIfstmt(self, ctx:BSVParser.IfstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#casestmt.
    def visitCasestmt(self, ctx:BSVParser.CasestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#casestmtitem.
    def visitCasestmtitem(self, ctx:BSVParser.CasestmtitemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#casestmtpatitem.
    def visitCasestmtpatitem(self, ctx:BSVParser.CasestmtpatitemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bigdefaultitem.
    def visitBigdefaultitem(self, ctx:BSVParser.BigdefaultitemContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#whilestmt.
    def visitWhilestmt(self, ctx:BSVParser.WhilestmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#forstmt.
    def visitForstmt(self, ctx:BSVParser.ForstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#forinit.
    def visitForinit(self, ctx:BSVParser.ForinitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#foroldinit.
    def visitForoldinit(self, ctx:BSVParser.ForoldinitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#simplevarassign.
    def visitSimplevarassign(self, ctx:BSVParser.SimplevarassignContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#fornewinit.
    def visitFornewinit(self, ctx:BSVParser.FornewinitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#simplevardeclassign.
    def visitSimplevardeclassign(self, ctx:BSVParser.SimplevardeclassignContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#fortest.
    def visitFortest(self, ctx:BSVParser.FortestContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#forincr.
    def visitForincr(self, ctx:BSVParser.ForincrContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#varincr.
    def visitVarincr(self, ctx:BSVParser.VarincrContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#condpredicate.
    def visitCondpredicate(self, ctx:BSVParser.CondpredicateContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#pattern.
    def visitPattern(self, ctx:BSVParser.PatternContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#constantpattern.
    def visitConstantpattern(self, ctx:BSVParser.ConstantpatternContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#taggedunionpattern.
    def visitTaggedunionpattern(self, ctx:BSVParser.TaggedunionpatternContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#structpattern.
    def visitStructpattern(self, ctx:BSVParser.StructpatternContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#tuplepattern.
    def visitTuplepattern(self, ctx:BSVParser.TuplepatternContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#attributeinstance.
    def visitAttributeinstance(self, ctx:BSVParser.AttributeinstanceContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#attrspec.
    def visitAttrspec(self, ctx:BSVParser.AttrspecContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#provisos.
    def visitProvisos(self, ctx:BSVParser.ProvisosContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#proviso.
    def visitProviso(self, ctx:BSVParser.ProvisoContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#fsmstmt.
    def visitFsmstmt(self, ctx:BSVParser.FsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#seqfsmstmt.
    def visitSeqfsmstmt(self, ctx:BSVParser.SeqfsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#parfsmstmt.
    def visitParfsmstmt(self, ctx:BSVParser.ParfsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#iffsmstmt.
    def visitIffsmstmt(self, ctx:BSVParser.IffsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#returnfsmstmt.
    def visitReturnfsmstmt(self, ctx:BSVParser.ReturnfsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#whilefsmstmt.
    def visitWhilefsmstmt(self, ctx:BSVParser.WhilefsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#forfsminit.
    def visitForfsminit(self, ctx:BSVParser.ForfsminitContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#forfsmstmt.
    def visitForfsmstmt(self, ctx:BSVParser.ForfsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#repeatfsmstmt.
    def visitRepeatfsmstmt(self, ctx:BSVParser.RepeatfsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#loopbodyfsmstmt.
    def visitLoopbodyfsmstmt(self, ctx:BSVParser.LoopbodyfsmstmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#importbvi.
    def visitImportbvi(self, ctx:BSVParser.ImportbviContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bvistmt.
    def visitBvistmt(self, ctx:BSVParser.BvistmtContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bviportopt.
    def visitBviportopt(self, ctx:BSVParser.BviportoptContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bvimethodopt.
    def visitBvimethodopt(self, ctx:BSVParser.BvimethodoptContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bvimethodname.
    def visitBvimethodname(self, ctx:BSVParser.BvimethodnameContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bvimethodnames.
    def visitBvimethodnames(self, ctx:BSVParser.BvimethodnamesContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by BSVParser#bvischedule.
    def visitBvischedule(self, ctx:BSVParser.BvischeduleContext):
        return self.visitChildren(ctx)



del BSVParser