#include "Expr.h"

Expr::Expr(ExprType exprType)
  : exprType(InvalidType)
{
}

Expr::~Expr()
{
}

VarExpr::VarExpr(std::string name)
  : Expr(VarExprType), name(name), sourceName(name)
{
}

VarExpr::~VarExpr()
{
}

OperatorExpr::OperatorExpr(std::string op, std::shared_ptr<Expr> lhs)
    : Expr(OperatorExprType), op(op)
{
    subexprs.push_back(lhs);
}

OperatorExpr::OperatorExpr(std::string op, std::shared_ptr<Expr> lhs, std::shared_ptr<Expr> rhs)
    : Expr(OperatorExprType), op(op)
{
    subexprs.push_back(lhs);
    subexprs.push_back(rhs);
}

OperatorExpr::~OperatorExpr()
{
}
