
#include <fstream>
#include <iostream>
#include <memory>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdefaulted-function-deleted"
#include <BSVParser.h>
#pragma GCC diagnostic pop

#include "AttributeInstanceVisitor.h"
#include "BSVType.h"
#include "Expr.h"
#include "Pattern.h"
#include "Stmt.h"
#include "TypeChecker.h"

class GenerateAst {
    shared_ptr<TypeChecker> typeChecker;
    string packageName;
    ofstream logstream;
    AttributeInstanceVisitor aiv;
public:
    GenerateAst(const string &packageName, shared_ptr<TypeChecker> &typeChecker)
        : typeChecker(typeChecker), packageName(packageName), logstream(string("kami/") + packageName + string(".ast.log"), ostream::out) {}

    std::shared_ptr<PackageDefStmt> generateAst(BSVParser::PackagedefContext *ctx);

    void generateAst(BSVParser::PackagestmtContext *ctx, vector<std::shared_ptr<Stmt>> &stmts);

    std::shared_ptr<Stmt> generateAst(BSVParser::InterfacedeclContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::SubinterfacedefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::FunctiondefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::ModuledefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::MethoddefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::RuledefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::StmtContext *ctx);

    std::shared_ptr<LValue> lvalue(BSVParser::LvalueContext *lhs);

    std::shared_ptr<Expr> expr(BSVParser::ExpressionContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::CaseexprContext *ctx);

    std::shared_ptr<CaseExprItem> caseExprItem(BSVParser::CaseexpritemContext *ctx);

    std::shared_ptr<CaseExprItem> caseExprItem(BSVParser::CaseexprpatitemContext *ctx);

    std::shared_ptr<CaseExprItem> caseExprItem(BSVParser::CaseexprdefaultitemContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::CondexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::MatchesexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::BinopexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::UnopexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::ExprprimaryContext *ctx);

    shared_ptr<Expr> expr(BSVParser::FieldexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::TaggedunionexprContext *ctx);

    std::shared_ptr<Pattern> generateAst(BSVParser::PatternContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::VarbindingContext *varbinding);

    std::shared_ptr<Stmt> generateAst(BSVParser::VarassignContext *varassign);

    std::shared_ptr<Stmt> generateAst(BSVParser::ActionbindingContext *actionbinding);

    std::shared_ptr<Stmt> generateAst(BSVParser::ModuleinstContext *moduleinst);

private:
    string sourceLocation(antlr4::ParserRuleContext *pContext);
    SourcePos sourcePos(antlr4::ParserRuleContext *pContext);
};
