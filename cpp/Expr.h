#pragma once

#include <iostream>
#include <map>
#include <string>
#include <vector>
#include <memory>

#include "LexicalScope.h"
#include "Pattern.h"
#include "BSVType.h"
#include "SourcePos.h"

using namespace std;

enum ExprType {
    InvalidExprType,
    ArraySubExprType,
    BitSelExprType,
    VarExprType,
    IntConstType,
    InterfaceExprType,
    StringConstType,
    OperatorExprType,
    CallExprType,
    FieldExprType,
    CondExprType,
    CaseExprType,
    EnumUnionStructExprType,
    MatchesExprType,
    ValueofExprType
};

class FieldExpr;

class VarExpr;

class BitSelExpr;

class CallExpr;

class CondExpr;

class IntConst;

class InterfaceExpr;

class StringConst;

class MatchesExpr;

class OperatorExpr;

class ArraySubExpr;

class EnumUnionStructExpr;

class ValueofExpr;

class Expr : public enable_shared_from_this<Expr> {
public:
    const ExprType exprType;
    const shared_ptr<BSVType> bsvtype;
    const SourcePos sourcePos;

    Expr(ExprType exprType, const SourcePos &sourcePos);
    Expr(ExprType exprType, const shared_ptr<BSVType> &bsvtype, const SourcePos &sourcePos);

    virtual ~Expr();

    virtual void prettyPrint(ostream &out, int depth = 0) = 0;

    virtual shared_ptr<BitSelExpr> bitSelExpr() { return shared_ptr<BitSelExpr>(); }

    virtual shared_ptr<FieldExpr> fieldExpr() { return shared_ptr<FieldExpr>(); }

    virtual shared_ptr<VarExpr> varExpr() { return shared_ptr<VarExpr>(); }

    virtual shared_ptr<CallExpr> callExpr() { return shared_ptr<CallExpr>(); }

    virtual shared_ptr<CondExpr> condExpr() { return shared_ptr<CondExpr>(); }

    virtual shared_ptr<IntConst> intConst() { return shared_ptr<IntConst>(); }

    virtual shared_ptr<InterfaceExpr> interfaceExpr() { return shared_ptr<InterfaceExpr>(); }

    virtual shared_ptr<MatchesExpr> matchesExpr() { return shared_ptr<MatchesExpr>(); }

    virtual shared_ptr<StringConst> stringConst() { return shared_ptr<StringConst>(); }

    virtual shared_ptr<OperatorExpr> operatorExpr() { return shared_ptr<OperatorExpr>(); }

    virtual shared_ptr<ArraySubExpr> arraySubExpr() { return shared_ptr<ArraySubExpr>(); }

    virtual shared_ptr<EnumUnionStructExpr> enumUnionStructExpr() { return shared_ptr<EnumUnionStructExpr>(); }

    virtual shared_ptr<ValueofExpr> valueofExpr() { return shared_ptr<ValueofExpr>(); }


    virtual shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames);
};

class FieldExpr : public Expr {
public:
    const shared_ptr<Expr> object;
    const string fieldName;
public:
    FieldExpr(const shared_ptr<Expr> &object, const string &fieldName, const shared_ptr<BSVType> &bsvtype, const SourcePos &sourcePos = SourcePos());

    virtual ~FieldExpr();

    virtual void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<FieldExpr> fieldExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;

};

class VarExpr : public Expr {
public:
    const string name;
    const string sourceName;
public:
    VarExpr(const string &name, const shared_ptr<BSVType> &bsvtype, const SourcePos &sourcePos = SourcePos());

    virtual ~VarExpr();

    virtual void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<VarExpr> varExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};


class CallExpr : public Expr {
public:
    const shared_ptr<Expr> function;
    const vector<shared_ptr<Expr>> args;
public:
    CallExpr(const shared_ptr<Expr> &function, const vector<shared_ptr<Expr>> &args, const SourcePos &sourcePos = SourcePos());

    virtual ~CallExpr();

    virtual void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<CallExpr> callExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class CondExpr : public Expr {
public:
    const shared_ptr<Expr> cond;
    const shared_ptr<Expr> thenExpr;
    const shared_ptr<Expr> elseExpr;

public:
    CondExpr(const shared_ptr<Expr> &cond, const shared_ptr<Expr> &thenExpr, const shared_ptr<Expr> &elseExpr, const SourcePos &sourcePos = SourcePos());

    virtual ~CondExpr();

    virtual void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<CondExpr> condExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class IntConst : public Expr {
public:
    const string repr;
    long value;
    long base;
    long width;
public:
    IntConst(const string &repr, const SourcePos &sourcePos = SourcePos());

    ~IntConst() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<IntConst> intConst() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class Stmt;

class InterfaceExpr : public Expr {
public:
    const vector<shared_ptr<Stmt>> stmts;
public:

    InterfaceExpr(const shared_ptr<BSVType> bsvtype, const SourcePos &sourcePos = SourcePos());

    ~InterfaceExpr() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<InterfaceExpr> interfaceExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class StringConst : public Expr {
public:
    const string repr;
public:
    StringConst(const string &repr, const SourcePos &sourcePos = SourcePos());

    ~StringConst() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<StringConst> stringConst() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class OperatorExpr : public Expr {
public:
    const string op;
    const shared_ptr<Expr> lhs;
    const shared_ptr<Expr> rhs;
public:

    OperatorExpr(const string &op, const shared_ptr<Expr> &lhs, const SourcePos &sourcePos = SourcePos());

    OperatorExpr(const string &op, const shared_ptr<Expr> &lhs, const shared_ptr<Expr> &rhs, const SourcePos &sourcePos = SourcePos());

    ~OperatorExpr() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<OperatorExpr> operatorExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class MatchesExpr : public Expr {
public:
    const shared_ptr<Expr> expr;
    const shared_ptr<Pattern> pattern;
    const vector<shared_ptr<Expr>> patterncond;
public:

    MatchesExpr(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern, const SourcePos &sourcePos = SourcePos());

    MatchesExpr(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern, const vector<shared_ptr<Expr>> &patterncond, const SourcePos &sourcePos = SourcePos());

    ~MatchesExpr() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<MatchesExpr> matchesExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;

    static shared_ptr<MatchesExpr> create(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern);
    static shared_ptr<MatchesExpr> create(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern,
            const vector<shared_ptr<Expr>> &patterncond);

};

class ArraySubExpr : public Expr {
public:
    ArraySubExpr(const shared_ptr<Expr> &array, const shared_ptr<Expr> &index, const SourcePos &sourcePos = SourcePos());

    virtual ~ArraySubExpr();

    void prettyPrint(ostream &out, int depth) override;

    shared_ptr<ArraySubExpr> arraySubExpr() override;

public:
    const shared_ptr<Expr> array;
    const shared_ptr<Expr> index;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class BitSelExpr : public Expr {
public:
    BitSelExpr(const shared_ptr<Expr> &value, const shared_ptr<Expr> &msb,
                 const shared_ptr<Expr> &lsb, const SourcePos &sourcePos = SourcePos());

    virtual ~BitSelExpr();

    void prettyPrint(ostream &out, int depth) override;

    shared_ptr<BitSelExpr> bitSelExpr() override;

public:
    const shared_ptr<Expr> value;
    const shared_ptr<Expr> msb;
    const shared_ptr<Expr> lsb;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};

class EnumUnionStructExpr : public Expr {
public:
    EnumUnionStructExpr(const string &tag, const vector<string> &keys,
                        const vector<shared_ptr<Expr>> &vals, const SourcePos &sourcePos = SourcePos());

    ~EnumUnionStructExpr() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<EnumUnionStructExpr> enumUnionStructExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;

public:
    const string tag;
    const vector<string> keys;
    const vector<shared_ptr<Expr>> vals;
};

class ValueofExpr : public Expr {
    shared_ptr<BSVType> argtype;
public:

    ValueofExpr(const shared_ptr<BSVType> argtype, const SourcePos &sourcePos = SourcePos());

    ~ValueofExpr() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<ValueofExpr> valueofExpr() override;

    shared_ptr<Expr> rename(string prefix, shared_ptr<LexicalScope> &renames) override;
};