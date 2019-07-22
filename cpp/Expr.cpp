#include "Expr.h"

Expr::Expr()
{
}

Expr::~Expr()
{
}

VarExpr::VarExpr(std::string name)
    : name(name), sourceName(name)
{
}

VarExpr::~VarExpr()
{
}

OperatorExpr::OperatorExpr(std::string op, std::shared_ptr<Expr> lhs)
    : op(op)
{
    subexprs.push_back(lhs);
}

OperatorExpr::OperatorExpr(std::string op, std::shared_ptr<Expr> lhs, std::shared_ptr<Expr> rhs)
    : op(op)
{
    subexprs.push_back(lhs);
    subexprs.push_back(rhs);
}

OperatorExpr::~OperatorExpr()
{
}
