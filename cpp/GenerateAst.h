
#include <memory>

#include <BSVParser.h>

#include "BSVType.h"
#include "Expr.h"
#include "Stmt.h"

class GenerateAst {
public:
    GenerateAst() {}

    std::shared_ptr<PackageDefStmt> generateAst(BSVParser::PackagedefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::PackagestmtContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::InterfacedeclContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::SubinterfacedefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::FunctiondefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::ModuledefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::MethoddefContext *ctx);

    std::shared_ptr<BSVType> bsvtype(BSVParser::BsvtypeContext *);

    std::shared_ptr<BSVType> bsvtype(BSVParser::TypedeftypeContext *);

    std::shared_ptr<Stmt> generateAst(BSVParser::RuledefContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::StmtContext *ctx);

    std::shared_ptr<LValue> lvalue(BSVParser::LvalueContext *lhs);

    std::shared_ptr<Expr> expr(BSVParser::ExpressionContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::CaseexpritemContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::CaseexprdefaultitemContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::CondexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::MatchesexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::BinopexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::UnopexprContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::ExprprimaryContext *ctx);

    std::shared_ptr<Expr> expr(BSVParser::TaggedunionexprContext *ctx);

    std::shared_ptr<Stmt> generateAst(BSVParser::VarbindingContext *varbinding);

    std::shared_ptr<Stmt> generateAst(BSVParser::VarassignContext *varassign);

    std::shared_ptr<Stmt> generateAst(BSVParser::ActionbindingContext *actionbinding);

    std::shared_ptr<Stmt> generateAst(BSVParser::ModuleinstContext *moduleinst);

    string sourceLocation(antlr4::ParserRuleContext *pContext);
};
