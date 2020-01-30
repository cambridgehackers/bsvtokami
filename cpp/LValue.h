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

class ArraySubLValue;
class FieldLValue;
class VarLValue;

class LValueAttrs {
public:
    map<string,shared_ptr<BSVType>> boundVars;
    map<string,shared_ptr<BSVType>> assignedVars;
    map<string,shared_ptr<BSVType>> freeVars;
};

class LValue : public enable_shared_from_this<LValue> {
public:
    const LValueType lvalueType;
    LValueAttrs attrs_;
    const LValueAttrs &attrs() { return attrs_; }
public:
    LValue(LValueType lvalueType = InvalidLValueType) : lvalueType(lvalueType) {};
    virtual ~LValue() {}

    virtual void prettyPrint(ostream &out, int depth) = 0;

    virtual shared_ptr<ArraySubLValue> arraySubLValue() { return shared_ptr<ArraySubLValue>(); }
    virtual shared_ptr<FieldLValue> fieldLValue() { return shared_ptr<FieldLValue>(); }
    virtual shared_ptr<VarLValue> varLValue() { return shared_ptr<VarLValue>(); }

    virtual shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope) = 0;

};

class VarLValue : public LValue {
public:
    const string name;
    const shared_ptr<BSVType> bsvtype;
    explicit VarLValue(const string &name, const shared_ptr<BSVType> &bsvtype);
    ~VarLValue() override;
    void prettyPrint(ostream &out, int depth) override;
    shared_ptr<VarLValue> varLValue() override;

    shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope) override;
};

class ArraySubLValue : public LValue {
public:
    const shared_ptr<Expr> array;
    const shared_ptr<Expr> index;

    explicit ArraySubLValue(const shared_ptr<Expr> &array, const shared_ptr<Expr> &index);
    ~ArraySubLValue() override;
    void prettyPrint(ostream &out, int depth) override;
    shared_ptr<ArraySubLValue> arraySubLValue() override;

    shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope) override;

    static shared_ptr<LValue> create(shared_ptr<Expr> array, const shared_ptr<Expr> &index);
};


class RangeSelLValue : public LValue {
public:
    const shared_ptr<Expr> bitarray;
    const shared_ptr<Expr> msb;
    const shared_ptr<Expr> lsb;


    explicit RangeSelLValue(const shared_ptr<Expr> &bitarray, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb);
    ~RangeSelLValue() override;
    void prettyPrint(ostream &out, int depth) override;
    shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope) override;

    static shared_ptr<LValue> create(shared_ptr<Expr> bitarray, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb);
};

class FieldLValue : public LValue {
public:
    const shared_ptr<Expr> obj;
    const string field;
    explicit FieldLValue(const shared_ptr<Expr> &obj, const string &field);
    ~FieldLValue() override;
    void prettyPrint(ostream &out, int depth) override;
    shared_ptr<FieldLValue> fieldLValue() override;

    shared_ptr<struct LValue> rename(string prefix, shared_ptr<LexicalScope> &scope) override;

    static shared_ptr<LValue> create(shared_ptr<Expr> obj, string basicString);
};


#endif //BSV_PARSER_LVALUE_H
