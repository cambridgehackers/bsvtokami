#include "GenerateAst.h"

std::shared_ptr<Expr> GenerateAst::expr(BSVParser::ExpressionContext *ctx)
{
    std::shared_ptr<Expr> result;
    return result;
}
std::shared_ptr<Expr> GenerateAst::expr(BSVParser::CaseexpritemContext *ctx)
{
    std::shared_ptr<Expr> result;
    return result;
}
std::shared_ptr<Expr> GenerateAst::expr(BSVParser::CaseexprdefaultitemContext *ctx)
{
    std::shared_ptr<Expr> result;
    return result;
}
std::shared_ptr<Expr> GenerateAst::expr(BSVParser::BinopexprContext *ctx)
{
    std::shared_ptr<Expr> lhs(expr(ctx->left));
    std::shared_ptr<Expr> rhs(expr(ctx->right));
    std::string op(ctx->op->getText());
    std::shared_ptr<Expr> result(new OperatorExpr(op, lhs, rhs));
    return result;
}
std::shared_ptr<Expr> GenerateAst::expr(BSVParser::UnopexprContext *ctx)
{
    std::shared_ptr<Expr> result;
    return result;
}
std::shared_ptr<Expr> GenerateAst::expr(BSVParser::ExprprimaryContext *ctx)
{
    std::shared_ptr<Expr> result;
    return result;
}

void GenerateAst::generateAst(BSVParser::PackagedefContext *ctx)
{
    std::vector<BSVParser::PackagestmtContext *> stmts = ctx->packagestmt();
    fprintf(stderr, "generateAst %lu stmts\n", stmts.size());
    for (size_t i = 0; i < stmts.size(); i++) {
        generateAst(stmts.at(i));
    }
}

void GenerateAst::generateAst(BSVParser::PackagestmtContext *ctx)
{
    if (ctx->moduledef() != NULL) {
        generateAst(ctx->moduledef());
    } else {
        fprintf(stderr, "packagestmt %s\n", ctx->getText().c_str());
    }
}

void GenerateAst::generateAst(BSVParser::ModuledefContext *ctx)
{
    BSVParser::ModuleprotoContext *moduleproto = ctx->moduleproto();
    std::string moduleName(moduleproto->lowerCaseIdentifier()->getText());
    fprintf(stderr, "moduledef %s\n", moduleName.c_str());
    std::vector<BSVParser::ModulestmtContext *> stmts = ctx->modulestmt();
    for (size_t i = 0; i < stmts.size(); i++) {
        BSVParser::ModulestmtContext *modstmt = stmts.at(i);
        if (modstmt->methoddef() != 0) {
            generateAst(modstmt->methoddef());
        } else if (modstmt->stmt() != 0) {
            BSVParser::StmtContext *stmt = modstmt->stmt();
            if (stmt->ruledef() != 0) {
                generateAst(stmt->ruledef());
            }
        }
    }
}

void GenerateAst::generateAst(BSVParser::MethoddefContext *ctx)
{
    std::string methodName(ctx->lowerCaseIdentifier(0)->getText());
    fprintf(stderr, "    methoddef %s\n", methodName.c_str());
    if (ctx->methodcond() != 0) {
        fprintf(stderr, "      when %s\n", ctx->methodcond()->getText().c_str());
        std::shared_ptr<Expr> guard(expr(ctx->methodcond()->expression()));
    }
    std::vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    for (size_t i = 0; i < stmts.size(); i++) {
        generateAst(stmts.at(i));
    }
}

void GenerateAst::generateAst(BSVParser::RuledefContext *ctx)
{
    std::string ruleName(ctx->lowerCaseIdentifier(0)->getText());
    fprintf(stderr, "    ruledef %s\n", ruleName.c_str());
    if (ctx->rulecond() != 0) {
        fprintf(stderr, "      when %s\n", ctx->rulecond()->getText().c_str());
        std::shared_ptr<Expr> guard(expr(ctx->rulecond()->expression()));
    }
    std::vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    for (size_t i = 0; i < stmts.size(); i++) {
        generateAst(stmts.at(i));
    }
}

void GenerateAst::generateAst(BSVParser::StmtContext *ctx)
{
    fprintf(stderr, "        stmt %s\n", ctx->getText().c_str());
}
