//
// Created by Jamey Hicks on 10/31/19.
//

#ifndef BSV_PARSER_LVALUE_H
#define BSV_PARSER_LVALUE_H

#include <memory>

#include "Expr.h"
#include "LexicalScope.h"

using namespace std;

enum LValueType {
    InvalidLValueType,
    ArraySubLValueType,
    FieldLValueType,
    VarLValueType,
    RangeSelLValueType
};

class VarLValue;

class LValue : public enable_shared_from_this<LValue> {
    LValueType lvalueType;
public:
    LValue(LValueType lvalueType = InvalidLValueType) : lvalueType(lvalueType) {};
    virtual ~LValue() {}

    virtual void prettyPrint(ostream &out, int depth) = 0;
    virtual shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope) = 0;

};

class VarLValue : public LValue {
public:
    const string name;
    static shared_ptr<VarLValue> create(const string &name);
    explicit VarLValue(const string &name);
    virtual ~VarLValue();
    virtual void prettyPrint(ostream &out, int depth);
    virtual shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope);
};

class ArraySubLValue : public LValue {
public:
    const shared_ptr<Expr> array;
    const shared_ptr<Expr> index;

    explicit ArraySubLValue(const shared_ptr<Expr> &array, const shared_ptr<Expr> &index);
    virtual ~ArraySubLValue();
    virtual void prettyPrint(ostream &out, int depth);
    virtual shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope);

    static shared_ptr<LValue> create(shared_ptr<Expr> array, const shared_ptr<Expr> &index);
};


class RangeSelLValue : public LValue {
public:
    const shared_ptr<Expr> bitarray;
    const shared_ptr<Expr> msb;
    const shared_ptr<Expr> lsb;


    explicit RangeSelLValue(const shared_ptr<Expr> &bitarray, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb);
    virtual ~RangeSelLValue();
    virtual void prettyPrint(ostream &out, int depth);
    virtual shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope);

    static shared_ptr<LValue> create(shared_ptr<Expr> bitarray, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb);
};

class FieldLValue : public LValue {
public:
    const shared_ptr<Expr> obj;
    const string field;
    explicit FieldLValue(const shared_ptr<Expr> &obj, const string &field);
    virtual ~FieldLValue();
    virtual void prettyPrint(ostream &out, int depth);
    virtual shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope);

    static shared_ptr<LValue> create(shared_ptr<Expr> obj, string basicString);
};


#endif //BSV_PARSER_LVALUE_H
