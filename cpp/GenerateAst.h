
#include <memory>

#include <BSVParser.h>

#include "Expr.h"

class GenerateAst {
 public:
  GenerateAst() {}

  void generateAst(BSVParser::PackagedefContext *ctx);
  void generateAst(BSVParser::PackagestmtContext *ctx);
  void generateAst(BSVParser::ModuledefContext *ctx);
  void generateAst(BSVParser::MethoddefContext *ctx);
  void generateAst(BSVParser::RuledefContext *ctx);
  void generateAst(BSVParser::StmtContext *ctx);

  std::shared_ptr<Expr> expr(BSVParser::ExpressionContext *ctx);
  std::shared_ptr<Expr> expr(BSVParser::CaseexpritemContext *ctx);
  std::shared_ptr<Expr> expr(BSVParser::CaseexprdefaultitemContext *ctx);
  std::shared_ptr<Expr> expr(BSVParser::BinopexprContext *ctx);
  std::shared_ptr<Expr> expr(BSVParser::UnopexprContext *ctx);
  std::shared_ptr<Expr> expr(BSVParser::ExprprimaryContext *ctx);
};
