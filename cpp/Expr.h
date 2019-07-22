
#include <string>
#include <vector>
#include <memory>

enum ExprType {
  InvalidType,
  VarExprType,
  OperatorExpr,
  CondExprType,
  CaseExprType
};

class Expr {
  ExprType exprType;
  
 public:
  Expr();
  virtual ~Expr();
};

class VarExpr : public Expr {
 private:
    std::string name;
    std::string sourceName;
 public:
    VarExpr(std::string name);
    virtual ~VarExpr();
};

class OperatorExpr : public Expr {
 private:
    std::string op;
    std::vector<std::shared_ptr<Expr>> subexprs;
 public:

    OperatorExpr(std::string op, std::shared_ptr<Expr> lhs);
    OperatorExpr(std::string op, std::shared_ptr<Expr> lhs, std::shared_ptr<Expr> rhs);
    virtual ~OperatorExpr();
};
