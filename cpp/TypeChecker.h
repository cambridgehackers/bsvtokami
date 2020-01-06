#pragma once

#include <assert.h>

#include <map>
#include <iostream>
#include "antlr4-runtime.h"
#include "z3++.h"
#include "z3_api.h"
#include "z3.h"

#include "BSVBaseVisitor.h"
#include "Declaration.h"
#include "LexicalScope.h"

using namespace std;

class PackageContext {
public:
    string packageName;
    vector<shared_ptr<Declaration> > declarationList;
    vector<shared_ptr<Declaration> > typeDeclarationList;
    map<string, shared_ptr<Declaration> > declaration;
    map<string, shared_ptr<Declaration> > typeDeclaration;
    multimap<string, shared_ptr<Declaration> > enumtag;
    multimap<string, shared_ptr<Declaration> > memberDeclaration;
    ofstream logstream;
    PackageContext(const string &packageName);

    void import(const shared_ptr<LexicalScope> &scope);

    void visitEnumDeclaration(const shared_ptr<EnumDeclaration> &decl);
    void visitInterfaceDeclaration(const shared_ptr<InterfaceDeclaration> &decl);
    void visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl);
    void visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl);
    void visitStructDeclaration(const shared_ptr<StructDeclaration> &decl);
    void visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl);
    void visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl);
};

/**
 * Static analyzer of BSV package
 */
class TypeChecker : public BSVBaseVisitor {

    // Z3 Solver information, reset when processing each module definition
    z3::context context;
    z3::solver solver;
    map<antlr4::ParserRuleContext *, z3::expr> exprs;
    map<string, antlr4::ParserRuleContext *> trackers;
    map<antlr4::ParserRuleContext *, shared_ptr<BSVType>> exprTypes;
    map<antlr4::ParserRuleContext *, shared_ptr<Declaration>> varDecls;
    map<string, z3::func_decl> typeDecls;
    map<string, z3::func_decl> typeRecognizers;
    z3::sort typeSort, intSort, boolSort;

    map<string, bool> boolops;

    shared_ptr<LexicalScope> lexicalScope;
    map<string, shared_ptr<LexicalScope>> packageScopes;
    shared_ptr<PackageContext> currentContext;

    bool actionContext;
    shared_ptr<Declaration> parentDecl;
    int nameCount;
    const vector<string> includePath;
    const vector<string> definitions;

public:
    TypeChecker(const string &packageName, const vector<string> &includePath, const vector<string> &definitions);
    ~TypeChecker();

    shared_ptr<BSVType> lookup(antlr4::ParserRuleContext *ctx);

    shared_ptr<BSVType> dereferenceType(const shared_ptr<BSVType> &bsvtype);

    BSVParser::PackagedefContext *analyzePackage(const string &packageName);

private:
    static const char *check_result_name[];

    string searchIncludePath(const string &pkgName);

    void setupZ3Context();

    void setupModuleFunctionConstructors();

    string freshString(string name);

    z3::symbol freshName(string name);

    z3::expr freshConstant(string name, z3::sort sort);

    z3::expr constant(string name, z3::sort sort);

    void insertExpr(antlr4::ParserRuleContext *ctx, z3::expr expr);

    void addConstraint(z3::expr constraint, const string &trackerPrefix, antlr4::ParserRuleContext *ctx);

    z3::expr orExprs(vector<z3::expr> exprs);

    void pushScope(const string &name) {
        lexicalScope = make_shared<LexicalScope>(name, lexicalScope);
    }

    void popScope() {
        lexicalScope = lexicalScope->parent;
    }

protected:

    void addDeclaration(BSVParser::PackagestmtContext *pkgstmt);
    void addDeclaration(BSVParser::InterfacedeclContext *interfacedecl);
    void addDeclaration(BSVParser::FunctiondefContext *functiondef);
    void addDeclaration(BSVParser::ModuledefContext *moduledef);
    void addDeclaration(BSVParser::TypeclassdeclContext *typeclassdecl);
    void addDeclaration(BSVParser::TypeclassinstanceContext *typeclassinstance);
    void addDeclaration(BSVParser::TypedefenumContext *enumdef);
    void addDeclaration(BSVParser::TypedefstructContext *structdef);
    void addDeclaration(BSVParser::TypedefsynonymContext *synonymdef);
    void addDeclaration(BSVParser::TypedeftaggedunionContext *uniondef);
    void addDeclaration(BSVParser::VarbindingContext *varbinding);

    antlrcpp::Any visitPackagedef(BSVParser::PackagedefContext *ctx) override;

    antlrcpp::Any visitPackagedecl(BSVParser::PackagedeclContext *ctx) override;

    antlrcpp::Any visitEndpackage(BSVParser::EndpackageContext *ctx) override;

    antlrcpp::Any visitLowerCaseIdentifier(BSVParser::LowerCaseIdentifierContext *ctx) override;

    antlrcpp::Any visitUpperCaseIdentifier(BSVParser::UpperCaseIdentifierContext *ctx) override;

    antlrcpp::Any visitAnyidentifier(BSVParser::AnyidentifierContext *ctx) override;

    antlrcpp::Any visitExportdecl(BSVParser::ExportdeclContext *ctx) override;

    antlrcpp::Any visitExportitem(BSVParser::ExportitemContext *ctx) override;

    antlrcpp::Any visitImportdecl(BSVParser::ImportdeclContext *ctx) override;

    antlrcpp::Any visitPackagestmt(BSVParser::PackagestmtContext *ctx) override;

    antlrcpp::Any visitPackageide(BSVParser::PackageideContext *ctx) override;

    antlrcpp::Any visitInterfacedecl(BSVParser::InterfacedeclContext *ctx) override;

    antlrcpp::Any visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) override;

    antlrcpp::Any visitMethodproto(BSVParser::MethodprotoContext *ctx) override;

    antlrcpp::Any visitMethodprotoformals(BSVParser::MethodprotoformalsContext *ctx) override;

    antlrcpp::Any visitMethodprotoformal(BSVParser::MethodprotoformalContext *formal) override;

    antlrcpp::Any visitSubinterfacedecl(BSVParser::SubinterfacedeclContext *ctx) override;

    antlrcpp::Any visitTypedeftype(BSVParser::TypedeftypeContext *ctx) override;

    antlrcpp::Any visitTypeformals(BSVParser::TypeformalsContext *ctx) override;

    antlrcpp::Any visitTypeformal(BSVParser::TypeformalContext *ctx) override;

    antlrcpp::Any visitTypedefsynonym(BSVParser::TypedefsynonymContext *ctx) override;

    antlrcpp::Any visitTypedefenum(BSVParser::TypedefenumContext *ctx) override;

    antlrcpp::Any visitTypedefenumelement(BSVParser::TypedefenumelementContext *ctx) override;

    antlrcpp::Any visitTypedefstruct(BSVParser::TypedefstructContext *ctx) override;

    antlrcpp::Any visitTypedeftaggedunion(BSVParser::TypedeftaggedunionContext *ctx) override;

    antlrcpp::Any visitStructmember(BSVParser::StructmemberContext *ctx) override;

    antlrcpp::Any visitUnionmember(BSVParser::UnionmemberContext *ctx) override;

    antlrcpp::Any visitSubstruct(BSVParser::SubstructContext *ctx) override;

    antlrcpp::Any visitSubunion(BSVParser::SubunionContext *ctx) override;

    antlrcpp::Any visitDerives(BSVParser::DerivesContext *ctx) override;

    antlrcpp::Any visitVarbinding(BSVParser::VarbindingContext *ctx) override;

    antlrcpp::Any visitActionbinding(BSVParser::ActionbindingContext *ctx) override;

    antlrcpp::Any visitPatternbinding(BSVParser::PatternbindingContext *ctx) override;

    antlrcpp::Any visitTypeclassdecl(BSVParser::TypeclassdeclContext *ctx) override;

    antlrcpp::Any visitTypeclasside(BSVParser::TypeclassideContext *ctx) override;

    antlrcpp::Any visitTypedepends(BSVParser::TypedependsContext *ctx) override;

    antlrcpp::Any visitTypedepend(BSVParser::TypedependContext *ctx) override;

    antlrcpp::Any visitTypelist(BSVParser::TypelistContext *ctx) override;

    antlrcpp::Any visitOverloadeddecl(BSVParser::OverloadeddeclContext *ctx) override;

    antlrcpp::Any visitTctype(BSVParser::TctypeContext *ctx) override;

    antlrcpp::Any visitTypeclassinstance(BSVParser::TypeclassinstanceContext *ctx) override;

    antlrcpp::Any visitOverloadeddef(BSVParser::OverloadeddefContext *ctx) override;

    antlrcpp::Any visitModuledef(BSVParser::ModuledefContext *ctx) override;

    antlrcpp::Any visitModuleproto(BSVParser::ModuleprotoContext *ctx) override;

    antlrcpp::Any visitModuleprotoformals(BSVParser::ModuleprotoformalsContext *ctx) override;

    antlrcpp::Any visitModuleprotoformal(BSVParser::ModuleprotoformalContext *formal) override;

    antlrcpp::Any visitModulestmt(BSVParser::ModulestmtContext *ctx) override;

    antlrcpp::Any visitModuleinst(BSVParser::ModuleinstContext *ctx) override;

    antlrcpp::Any visitMethoddef(BSVParser::MethoddefContext *ctx) override;

    antlrcpp::Any visitMethodformals(BSVParser::MethodformalsContext *ctx) override;

    antlrcpp::Any visitMethodformal(BSVParser::MethodformalContext *formal) override;

    antlrcpp::Any visitMethodcond(BSVParser::MethodcondContext *ctx) override;

    antlrcpp::Any visitSubinterfacedef(BSVParser::SubinterfacedefContext *ctx) override;

    antlrcpp::Any visitRuledef(BSVParser::RuledefContext *ctx) override;

    antlrcpp::Any visitRulecond(BSVParser::RulecondContext *ctx) override;

    antlrcpp::Any visitFunctiondef(BSVParser::FunctiondefContext *ctx) override;

    antlrcpp::Any visitFunctionproto(BSVParser::FunctionprotoContext *ctx) override;

    antlrcpp::Any visitExterncimport(BSVParser::ExterncimportContext *ctx) override;

    antlrcpp::Any visitExterncfuncargs(BSVParser::ExterncfuncargsContext *ctx) override;

    antlrcpp::Any visitExterncfuncarg(BSVParser::ExterncfuncargContext *ctx) override;

    antlrcpp::Any visitVarassign(BSVParser::VarassignContext *ctx) override;

    z3::expr visitLIndexValue(BSVParser::ExprprimaryContext *ctx, BSVParser::ExpressionContext *index);

    z3::expr visitLFieldValue(BSVParser::ExprprimaryContext *ctx, string fieldname);

    antlrcpp::Any visitLvalue(BSVParser::LvalueContext *ctx) override;

    antlrcpp::Any visitBsvtype(BSVParser::BsvtypeContext *ctx) override;

    antlrcpp::Any visitTypeide(BSVParser::TypeideContext *ctx) override;

    antlrcpp::Any visitTypenat(BSVParser::TypenatContext *ctx) override;

    antlrcpp::Any visitOperatorexpr(BSVParser::OperatorexprContext *ctx) override;

    antlrcpp::Any visitCaseexpr(BSVParser::CaseexprContext *ctx) override;

    antlrcpp::Any visitMatchesexpr(BSVParser::MatchesexprContext *ctx) override;

    antlrcpp::Any visitCondexpr(BSVParser::CondexprContext *ctx) override;

    antlrcpp::Any visitCaseexpritem(BSVParser::CaseexpritemContext *ctx) override;

    antlrcpp::Any visitPatterncond(BSVParser::PatterncondContext *ctx) override;

    antlrcpp::Any visitBinopexpr(BSVParser::BinopexprContext *ctx) override;

    antlrcpp::Any visitUnopexpr(BSVParser::UnopexprContext *ctx) override;

    antlrcpp::Any visitBitconcat(BSVParser::BitconcatContext *ctx) override;

    antlrcpp::Any visitVarexpr(BSVParser::VarexprContext *ctx) override;

    antlrcpp::Any visitBlockexpr(BSVParser::BlockexprContext *ctx) override;

    antlrcpp::Any visitStringliteral(BSVParser::StringliteralContext *ctx) override;

    antlrcpp::Any visitIntliteral(BSVParser::IntliteralContext *ctx) override;

    antlrcpp::Any visitRealliteral(BSVParser::RealliteralContext *ctx) override;

    antlrcpp::Any visitCastexpr(BSVParser::CastexprContext *ctx) override;

    antlrcpp::Any visitTypeassertionexpr(BSVParser::TypeassertionexprContext *ctx) override;

    antlrcpp::Any visitResetbyexpr(BSVParser::ResetbyexprContext *ctx) override;

    antlrcpp::Any visitUndefinedexpr(BSVParser::UndefinedexprContext *ctx) override;

    antlrcpp::Any visitClockedbyexpr(BSVParser::ClockedbyexprContext *ctx) override;

    antlrcpp::Any visitFieldexpr(BSVParser::FieldexprContext *ctx) override;

    antlrcpp::Any visitParenexpr(BSVParser::ParenexprContext *ctx) override;

    shared_ptr<BSVType> resolveInterfaceTag(shared_ptr<BSVType> interfaceTypeOrTag);

    antlrcpp::Any visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) override;

    antlrcpp::Any visitCallexpr(BSVParser::CallexprContext *ctx) override;

    antlrcpp::Any visitSyscallexpr(BSVParser::SyscallexprContext *ctx) override;

    antlrcpp::Any visitValueofexpr(BSVParser::ValueofexprContext *ctx) override;

    antlrcpp::Any visitTaggedunionexpr(BSVParser::TaggedunionexprContext *ctx) override;

    antlrcpp::Any visitArraysub(BSVParser::ArraysubContext *ctx) override;

    antlrcpp::Any visitMemberbinds(BSVParser::MemberbindsContext *ctx) override;

    antlrcpp::Any visitMemberbind(BSVParser::MemberbindContext *ctx) override;

    antlrcpp::Any visitInterfacestmt(BSVParser::InterfacestmtContext *ctx) override;

    antlrcpp::Any visitBeginendblock(BSVParser::BeginendblockContext *ctx) override;

    antlrcpp::Any visitRegwrite(BSVParser::RegwriteContext *ctx) override;

    antlrcpp::Any visitStmt(BSVParser::StmtContext *ctx) override;

    antlrcpp::Any visitIfstmt(BSVParser::IfstmtContext *ctx) override;

    antlrcpp::Any visitCasestmt(BSVParser::CasestmtContext *ctx) override;

    antlrcpp::Any visitCasestmtdefaultitem(BSVParser::CasestmtdefaultitemContext *ctx) override;

    antlrcpp::Any visitWhilestmt(BSVParser::WhilestmtContext *ctx) override;

    antlrcpp::Any visitForstmt(BSVParser::ForstmtContext *ctx) override;

    antlrcpp::Any visitForinit(BSVParser::ForinitContext *ctx) override;

    antlrcpp::Any visitSimplevardeclassign(BSVParser::SimplevardeclassignContext *ctx) override;

    antlrcpp::Any visitFortest(BSVParser::FortestContext *ctx) override;

    antlrcpp::Any visitForincr(BSVParser::ForincrContext *ctx) override;

    antlrcpp::Any visitVarincr(BSVParser::VarincrContext *ctx) override;

    antlrcpp::Any visitPattern(BSVParser::PatternContext *ctx) override;

    antlrcpp::Any visitConstantpattern(BSVParser::ConstantpatternContext *ctx) override;

    antlrcpp::Any visitTaggedunionpattern(BSVParser::TaggedunionpatternContext *ctx) override;

    antlrcpp::Any visitTuplepattern(BSVParser::TuplepatternContext *ctx) override;

    antlrcpp::Any visitProvisos(BSVParser::ProvisosContext *ctx) override;

    antlrcpp::Any visitProviso(BSVParser::ProvisoContext *ctx) override;

    antlrcpp::Any visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) override;

    antlrcpp::Any visitAttrspec(BSVParser::AttrspecContext *ctx) override;

    shared_ptr<BSVType> bsvtype(z3::expr v, z3::model mod);

public:
    shared_ptr<BSVType> bsvtype(BSVParser::BsvtypeContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::TypeformalContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::TypedeftypeContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::MethodprotoformalContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::MethodprotoContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::MethodformalContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::MethoddefContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::ModuleprotoContext *ctx);

    shared_ptr<BSVType> bsvtype(BSVParser::ModuleprotoformalContext *ctx);

    static string sourceLocation(antlr4::ParserRuleContext *pContext);

    z3::expr instantiateType(z3::func_decl type_decl, const z3::expr_vector &params);

    z3::expr instantiateType(const string &type_name, const z3::expr_vector &params);

    z3::expr instantiateType(const string &type_name);

    z3::expr instantiateType(const string &type_name, const z3::expr &param0);

    z3::expr instantiateType(const string &type_name, const z3::expr &param0, const z3::expr &param1);

    z3::expr bsvTypeToExpr(shared_ptr<BSVType> bsvtype, map<string,string> &varmapping);

    z3::expr bsvTypeToExpr(shared_ptr<BSVType> bsvtype);
};
