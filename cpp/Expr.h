
#include <string>
#include <vector>
#include <memory>

enum ExprType {
  InvalidType,
  VarExprType,
  OperatorExprType,
  CondExprType,
  CaseExprType
};

class Expr {
 protected:
  ExprType exprType;
  
 public:
  Expr(ExprType exprType);
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
