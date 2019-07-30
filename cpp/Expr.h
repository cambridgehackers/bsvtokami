#pragma once

#include <map>
#include <string>
#include <vector>
#include <memory>

#include "LexicalScope.h"

using namespace std;

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

class FieldExpr;

class VarExpr;

class CallExpr;

class IntConst;

class OperatorExpr;

class ArraySubExpr;

class EnumUnionStructExpr;

class Expr : public enable_shared_from_this<Expr> {
protected:
    ExprType exprType;

public:
    Expr(ExprType exprType);

    virtual ~Expr();

    virtual void prettyPrint(int depth = 0) = 0;

    virtual shared_ptr<FieldExpr> fieldExpr() { return shared_ptr<FieldExpr>(); }

    virtual shared_ptr<VarExpr> varExpr() { return shared_ptr<VarExpr>(); }

    virtual shared_ptr<CallExpr> callExpr() { return shared_ptr<CallExpr>(); }

    virtual shared_ptr<IntConst> intConst() { return shared_ptr<IntConst>(); }

    virtual shared_ptr<OperatorExpr> operatorExpr() { return shared_ptr<OperatorExpr>(); }

    virtual shared_ptr<ArraySubExpr> arraySubExpr() { return shared_ptr<ArraySubExpr>(); }

    virtual shared_ptr<EnumUnionStructExpr> enumUnionStructExpr() { return shared_ptr<EnumUnionStructExpr>(); }

    virtual shared_ptr<Expr> rename(string prefix, LexicalScope &renames);
};

class FieldExpr : public Expr {
public:
    const shared_ptr<Expr> object;
    const string fieldName;
public:
    FieldExpr(const shared_ptr<Expr> &object, const string &fieldName);

    virtual ~FieldExpr();

    virtual void prettyPrint(int depth = 0) override;

    shared_ptr<FieldExpr> fieldExpr() override;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;

};

class VarExpr : public Expr {
public:
    const string name;
    const string sourceName;
public:
    VarExpr(const string &name);

    virtual ~VarExpr();

    virtual void prettyPrint(int depth = 0) override;

    shared_ptr<VarExpr> varExpr() override;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;
};


class CallExpr : public Expr {
public:
    const shared_ptr<Expr> function;
    const vector<shared_ptr<Expr>> args;
public:
    CallExpr(const shared_ptr<Expr> &function, const vector<shared_ptr<Expr>> &args);

    virtual ~CallExpr();

    virtual void prettyPrint(int depth = 0) override;

    virtual shared_ptr<CallExpr> callExpr() override;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;
};

class IntConst : public Expr {
public:
    const string repr;
    long value;
    long base;
    long width;
public:
    IntConst(const string &repr);

    ~IntConst() override;

    void prettyPrint(int depth = 0) override;

    shared_ptr<IntConst> intConst() override;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;
};


class OperatorExpr : public Expr {
public:
    const string op;
    const shared_ptr<Expr> lhs;
    const shared_ptr<Expr> rhs;
public:

    OperatorExpr(const string &op, const shared_ptr<Expr> &lhs);

    OperatorExpr(const string &op, const shared_ptr<Expr> &lhs, const shared_ptr<Expr> &rhs);

    ~OperatorExpr() override;

    void prettyPrint(int depth = 0) override;

    shared_ptr<OperatorExpr> operatorExpr() override;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;
};

class ArraySubExpr : public Expr {
public:
    ArraySubExpr(const shared_ptr<Expr> &array, const shared_ptr<Expr> &msb,
                 const shared_ptr<Expr> &lsb);

    virtual ~ArraySubExpr();

    void prettyPrint(int depth) override;

    shared_ptr<ArraySubExpr> arraySubExpr() override;

public:
    const shared_ptr<Expr> array;
    const shared_ptr<Expr> msb;
    const shared_ptr<Expr> lsb;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;
};

class EnumUnionStructExpr : public Expr {
public:
    EnumUnionStructExpr(const string &tag, const vector<string> &keys,
                        const vector<shared_ptr<Expr>> &vals);

    ~EnumUnionStructExpr() override {}

    void prettyPrint(int depth = 0) override;

    shared_ptr<EnumUnionStructExpr> enumUnionStructExpr() override;

    shared_ptr<Expr> rename(string prefix, LexicalScope &renames) override;

public:
    const string tag;
    const vector<string> keys;
    const vector<shared_ptr<Expr>> vals;
};
