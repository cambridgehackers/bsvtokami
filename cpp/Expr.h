#pragma once

#include <string>
#include <vector>
#include <memory>

enum ExprType {
    InvalidExprType,
    ArraySubExprType,
    VarExprType,
    IntConstType,
    OperatorExprType,
    CallExprType,
    FieldExprType,
    CondExprType,
    CaseExprType,
    EnumUnionStructExprType
};

class Expr {
protected:
    ExprType exprType;

public:
    Expr(ExprType exprType);

    virtual ~Expr();

    virtual void prettyPrint(int depth = 0) = 0;
};

class FieldExpr : public Expr {
private:
    std::shared_ptr<Expr> object;
    std::string fieldName;
public:
    FieldExpr(std::shared_ptr<Expr> object, std::string fieldName);

    virtual ~FieldExpr();

    virtual void prettyPrint(int depth = 0);
};

class VarExpr : public Expr {
private:
    std::string name;
    std::string sourceName;
public:
    VarExpr(std::string name);

    virtual ~VarExpr();

    virtual void prettyPrint(int depth = 0);
};


class CallExpr : public Expr {
private:
    std::shared_ptr<Expr> function;
    std::vector<std::shared_ptr<Expr>> args;
public:
    CallExpr(const std::shared_ptr<Expr> &function, const std::vector<std::shared_ptr<Expr>> &args);

    virtual ~CallExpr();

    virtual void prettyPrint(int depth = 0);
};

class IntConst : public Expr {
private:
    std::string repr;
    long value;
    long base;
    long width;
public:
    IntConst(std::string repr);

    ~IntConst() override;

    void prettyPrint(int depth = 0) override;
};


class OperatorExpr : public Expr {
private:
    std::string op;
    std::shared_ptr<Expr> lhs;
    std::shared_ptr<Expr> rhs;
public:

    OperatorExpr(std::string op, std::shared_ptr<Expr> lhs);

    OperatorExpr(std::string op, std::shared_ptr<Expr> lhs, std::shared_ptr<Expr> rhs);

    ~OperatorExpr() override;

    void prettyPrint(int depth = 0) override;
};

class ArraySubExpr : public Expr {
public:
    ArraySubExpr( const std::shared_ptr<Expr> &array, const std::shared_ptr<Expr> &msb,
                 const std::shared_ptr<Expr> &lsb);

    virtual ~ArraySubExpr();

    void prettyPrint(int depth) override;

private:
    std::shared_ptr<Expr> array;
    std::shared_ptr<Expr> msb;
    std::shared_ptr<Expr> lsb;
};

class EnumUnionStructExpr : public Expr {
public:
    EnumUnionStructExpr(const std::string &tag, const std::vector<std::string> &keys,
                        const std::vector<std::shared_ptr<Expr>> &vals);
    ~EnumUnionStructExpr() override {}

    void prettyPrint(int depth = 0) override;

private:
    std::string tag;
    std::vector<std::string> keys;
    std::vector<std::shared_ptr<Expr>> vals;
};
