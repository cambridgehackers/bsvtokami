#pragma once

#include "antlr4-runtime.h"
#include "BSVBaseVisitor.h"

/**
 * Static analyzer of BSV package
 */
class  StaticAnalyzer : public BSVBaseVisitor {
public:
    StaticAnalyzer() {
    }

    virtual antlrcpp::Any visitPackagedef(BSVParser::PackagedefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackagedecl(BSVParser::PackagedeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitEndpackage(BSVParser::EndpackageContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLowerCaseIdentifier(BSVParser::LowerCaseIdentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUpperCaseIdentifier(BSVParser::UpperCaseIdentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIdentifier(BSVParser::IdentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitAnyidentifier(BSVParser::AnyidentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExportdecl(BSVParser::ExportdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExportitem(BSVParser::ExportitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitImportdecl(BSVParser::ImportdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitImportitem(BSVParser::ImportitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackagestmt(BSVParser::PackagestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackageide(BSVParser::PackageideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfacedecl(BSVParser::InterfacedeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodproto(BSVParser::MethodprotoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodprotoformals(BSVParser::MethodprotoformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodprotoformal(BSVParser::MethodprotoformalContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubinterfacedecl(BSVParser::SubinterfacedeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedecl(BSVParser::TypedeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedeftype(BSVParser::TypedeftypeContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeformals(BSVParser::TypeformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeformal(BSVParser::TypeformalContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefsynonym(BSVParser::TypedefsynonymContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefenum(BSVParser::TypedefenumContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefenumelement(BSVParser::TypedefenumelementContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefstruct(BSVParser::TypedefstructContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedeftaggedunion(BSVParser::TypedeftaggedunionContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStructmember(BSVParser::StructmemberContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUnionmember(BSVParser::UnionmemberContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubstruct(BSVParser::SubstructContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubunion(BSVParser::SubunionContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitDerives(BSVParser::DerivesContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarBinding(BSVParser::VarBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionBinding(BSVParser::ActionBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLetBinding(BSVParser::LetBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPatternBinding(BSVParser::PatternBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarinit(BSVParser::VarinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitArraydims(BSVParser::ArraydimsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeclassdecl(BSVParser::TypeclassdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeclasside(BSVParser::TypeclassideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedepends(BSVParser::TypedependsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedepend(BSVParser::TypedependContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypelist(BSVParser::TypelistContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitOverloadeddecl(BSVParser::OverloadeddeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTctype(BSVParser::TctypeContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeclassinstance(BSVParser::TypeclassinstanceContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitOverloadeddef(BSVParser::OverloadeddefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuledef(BSVParser::ModuledefContext *ctx) override {
        fprintf(stderr, "ModuleDef %s\n", ctx->moduleproto()->name->getText().c_str());
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleproto(BSVParser::ModuleprotoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModulestmt(BSVParser::ModulestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleinst(BSVParser::ModuleinstContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleapp(BSVParser::ModuleappContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleactualparamarg(BSVParser::ModuleactualparamargContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethoddef(BSVParser::MethoddefContext *ctx) override {
        fprintf(stderr, "    ModuleDef %s\n", ctx->name->getText().c_str());
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodformals(BSVParser::MethodformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodformal(BSVParser::MethodformalContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodcond(BSVParser::MethodcondContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubinterfacedef(BSVParser::SubinterfacedefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRuledef(BSVParser::RuledefContext *ctx) override {
        fprintf(stderr, "    RuleDef %s\n", ctx->name->getText().c_str());
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulecond(BSVParser::RulecondContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulebody(BSVParser::RulebodyContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFunctiondef(BSVParser::FunctiondefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFunctionproto(BSVParser::FunctionprotoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExterncimport(BSVParser::ExterncimportContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExterncfuncargs(BSVParser::ExterncfuncargsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExterncfuncarg(BSVParser::ExterncfuncargContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarassign(BSVParser::VarassignContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLvalue(BSVParser::LvalueContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBsvtype(BSVParser::BsvtypeContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeide(BSVParser::TypeideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypenat(BSVParser::TypenatContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitOperatorexpr(BSVParser::OperatorexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCaseexpr(BSVParser::CaseexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMatchesexpr(BSVParser::MatchesexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCondexpr(BSVParser::CondexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTripleandexpr(BSVParser::TripleandexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCaseexpritem(BSVParser::CaseexpritemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPatterncond(BSVParser::PatterncondContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBinopexpr(BSVParser::BinopexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUnopexpr(BSVParser::UnopexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBitconcat(BSVParser::BitconcatContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarexpr(BSVParser::VarexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBlockexpr(BSVParser::BlockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParfsmexpr(BSVParser::ParfsmexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStructexpr(BSVParser::StructexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStringliteral(BSVParser::StringliteralContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulesexpr(BSVParser::RulesexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIntliteral(BSVParser::IntliteralContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRealliteral(BSVParser::RealliteralContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCastexpr(BSVParser::CastexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeassertionexpr(BSVParser::TypeassertionexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitResetbyexpr(BSVParser::ResetbyexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUndefinedexpr(BSVParser::UndefinedexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitClockedbyexpr(BSVParser::ClockedbyexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitReturnexpr(BSVParser::ReturnexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFieldexpr(BSVParser::FieldexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParenexpr(BSVParser::ParenexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionblockexpr(BSVParser::ActionblockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCallexpr(BSVParser::CallexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitValueofexpr(BSVParser::ValueofexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTaggedunionexpr(BSVParser::TaggedunionexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitArraysub(BSVParser::ArraysubContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionvalueblockexpr(BSVParser::ActionvalueblockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSeqfsmexpr(BSVParser::SeqfsmexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMemberbinds(BSVParser::MemberbindsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMemberbind(BSVParser::MemberbindContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfacestmt(BSVParser::InterfacestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulesstmt(BSVParser::RulesstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBeginendblock(BSVParser::BeginendblockContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionblock(BSVParser::ActionblockContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionvalueblock(BSVParser::ActionvalueblockContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRegwrite(BSVParser::RegwriteContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStmt(BSVParser::StmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIfstmt(BSVParser::IfstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmt(BSVParser::CasestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmtitem(BSVParser::CasestmtitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmtpatitem(BSVParser::CasestmtpatitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmtdefaultitem(BSVParser::CasestmtdefaultitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitWhilestmt(BSVParser::WhilestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForstmt(BSVParser::ForstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForinit(BSVParser::ForinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForoldinit(BSVParser::ForoldinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSimplevarassign(BSVParser::SimplevarassignContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFornewinit(BSVParser::FornewinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSimplevardeclassign(BSVParser::SimplevardeclassignContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFortest(BSVParser::FortestContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForincr(BSVParser::ForincrContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarincr(BSVParser::VarincrContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPattern(BSVParser::PatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitConstantpattern(BSVParser::ConstantpatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTaggedunionpattern(BSVParser::TaggedunionpatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStructpattern(BSVParser::StructpatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTuplepattern(BSVParser::TuplepatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitAttrspec(BSVParser::AttrspecContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitProvisos(BSVParser::ProvisosContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitProviso(BSVParser::ProvisoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFsmstmt(BSVParser::FsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSeqfsmstmt(BSVParser::SeqfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParfsmstmt(BSVParser::ParfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIffsmstmt(BSVParser::IffsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitReturnfsmstmt(BSVParser::ReturnfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitWhilefsmstmt(BSVParser::WhilefsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForfsminit(BSVParser::ForfsminitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForfsmstmt(BSVParser::ForfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRepeatfsmstmt(BSVParser::RepeatfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLoopbodyfsmstmt(BSVParser::LoopbodyfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPortide(BSVParser::PortideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitImportbvi(BSVParser::ImportbviContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvistmt(BSVParser::BvistmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBviportopt(BSVParser::BviportoptContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvimethodopt(BSVParser::BvimethodoptContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvimethodname(BSVParser::BvimethodnameContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvimethodnames(BSVParser::BvimethodnamesContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvischedule(BSVParser::BvischeduleContext *ctx) override {
        return visitChildren(ctx);
    }

};
