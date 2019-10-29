#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include <iostream>

using namespace std;

#include "Expr.h"

Expr::Expr(ExprType exprType)
        : exprType(exprType) {
}

Expr::~Expr() {
}

shared_ptr<Expr> Expr::rename(string prefix, LexicalScope &scope) {
    cerr << "Unhandled rename";
    prettyPrint(4);
    return shared_ptr<Expr>();
}

VarExpr::VarExpr(const string &name)
        : Expr(VarExprType), name(name), sourceName(name) {
}

VarExpr::~VarExpr() {
}

void VarExpr::prettyPrint(int depth) {
    cout << name;
}

shared_ptr<VarExpr> VarExpr::varExpr() { return static_pointer_cast<VarExpr, Expr>(shared_from_this()); }

shared_ptr<Expr> VarExpr::rename(string prefix, LexicalScope &scope) {
    string renamed = scope.lookup(name);
    if (!renamed.size())
        renamed = name;
    return shared_ptr<VarExpr>(new VarExpr(renamed));
}

IntConst::IntConst(const string &repr)
        : Expr(IntConstType), repr(repr), base(0), width(0) {
    const char *repr_ptr = repr.c_str();
    const char *quote_ptr = strchr(repr_ptr, '\'');
    const char *base_ptr = (quote_ptr) ? quote_ptr + 1 : repr_ptr;
    if (!quote_ptr || quote_ptr == repr_ptr) {
        width = 0;
    } else {
        width = strtoul(repr_ptr, 0, 10);
    }
    char base_char = base_ptr[0];
    switch (base_char) {
        case 'b':
            base = 2;
            break;
        case 'o':
            base = 8;
            break;
        case 'd':
            base = 10;
            break;
        case 'h':
            base = 16;
            break;
    }
    const char *value_ptr = (base) ? base_ptr + 1 : base_ptr;
    value = strtoul(base_ptr, 0, base);
    //fprintf(stderr, "%s width=%ld base=%ld value=%ld\n", repr.c_str(), width, base, value);
}

IntConst::~IntConst() {
}

void IntConst::prettyPrint(int depth) {
    cout << repr;
}

shared_ptr<IntConst> IntConst::intConst() { return static_pointer_cast<IntConst, Expr>(shared_from_this()); }

shared_ptr<Expr> IntConst::rename(string prefix, LexicalScope &scope) {
    return shared_ptr<IntConst>(new IntConst(repr));
}

OperatorExpr::OperatorExpr(const string &op, const shared_ptr<Expr> &lhs)
        : Expr(OperatorExprType), op(op), lhs(lhs) {
    assert(lhs);
}

OperatorExpr::OperatorExpr(const string &op, const shared_ptr<Expr> &lhs, const shared_ptr<Expr> &rhs)
        : Expr(OperatorExprType), op(op), lhs(lhs), rhs(rhs) {
    assert(lhs);
}

OperatorExpr::~OperatorExpr() {
}

void OperatorExpr::prettyPrint(int depth) {
    if (!rhs) {
        cout << op << " ";
    }
    lhs->prettyPrint(depth + 1);
    if (rhs) {
        cout << " " << op << " ";
        rhs->prettyPrint(depth + 1);
    }
}

shared_ptr<OperatorExpr> OperatorExpr::operatorExpr() {
    return static_pointer_cast<OperatorExpr, Expr>(shared_from_this());
}

shared_ptr<Expr> OperatorExpr::rename(string prefix, LexicalScope &scope) {
    if (rhs)
        return shared_ptr<OperatorExpr>(new OperatorExpr(op, lhs->rename(prefix, scope), rhs->rename(prefix, scope)));
    else
        return shared_ptr<OperatorExpr>(new OperatorExpr(op, lhs->rename(prefix, scope)));
}

FieldExpr::FieldExpr(const shared_ptr<Expr> &object, const std::string &fieldName)
        : Expr(FieldExprType), object(object), fieldName(fieldName) {
}

FieldExpr::~FieldExpr() {

}

void FieldExpr::prettyPrint(int depth) {
    object->prettyPrint(depth + 1);
    cout << "." << fieldName;
}

shared_ptr<FieldExpr> FieldExpr::fieldExpr() { return static_pointer_cast<FieldExpr, Expr>(shared_from_this()); }

shared_ptr<Expr> FieldExpr::rename(string prefix, LexicalScope &scope) {
    return shared_ptr<FieldExpr>(new FieldExpr(object->rename(prefix, scope), fieldName));
}

CallExpr::CallExpr(const shared_ptr<Expr> &function, const vector<shared_ptr<Expr>> &args) : Expr(
        CallExprType), function(function), args(args) {

}

CallExpr::~CallExpr() {

}

void CallExpr::prettyPrint(int depth) {
    function->prettyPrint(depth + 1);
    cout << "(";
    for (size_t i = 0; i < args.size(); i++) {
        if (i > 0)
            cout << ", ";
        if (args[i])
            args[i]->prettyPrint(depth + 1);
        else
            cout << "emptyarg:" << to_string(i);
    }
    cout << ")";
}

shared_ptr<CallExpr> CallExpr::callExpr() { return static_pointer_cast<CallExpr, Expr>(shared_from_this()); }

shared_ptr<Expr> CallExpr::rename(string prefix, LexicalScope &scope) {
    vector<shared_ptr<Expr>> renamedArgs;
    for (size_t i = 0; i < args.size(); i++)
        renamedArgs.push_back(args[i]->rename(prefix, scope));
    return shared_ptr<CallExpr>(new CallExpr(function->rename(prefix, scope), renamedArgs));
}


EnumUnionStructExpr::EnumUnionStructExpr(const string &tag, const vector<string> &keys,
                                         const vector<shared_ptr<Expr>> &vals) : Expr(EnumUnionStructExprType),
                                                                                 tag(tag), keys(keys),
                                                                                 vals(vals) {}

void EnumUnionStructExpr::prettyPrint(int depth) {
    cout << tag << " {";
    for (size_t i = 0; i < keys.size(); i++) {
        if (i > 0)
            cout << ";";
        cout << " " << keys.at(i) << ": ";
        vals.at(i)->prettyPrint(depth + 1);
    }
    cout << " }";
}

shared_ptr<EnumUnionStructExpr> EnumUnionStructExpr::enumUnionStructExpr() {
    return static_pointer_cast<EnumUnionStructExpr, Expr>(shared_from_this());
}

shared_ptr<Expr> EnumUnionStructExpr::rename(string prefix, LexicalScope &scope) {
    vector<shared_ptr<Expr>> renamedVals;
    for (size_t i = 0; i < vals.size(); i++)
        renamedVals.push_back(vals[i]->rename(prefix, scope));
    return shared_ptr<EnumUnionStructExpr>(new EnumUnionStructExpr(tag, keys, renamedVals));
}


ArraySubExpr::ArraySubExpr(const shared_ptr<Expr> &array, const shared_ptr<Expr> &msb,
                           const shared_ptr<Expr> &lsb) : Expr(ArraySubExprType), array(array), msb(msb), lsb(lsb) {}

ArraySubExpr::~ArraySubExpr() {

}

void ArraySubExpr::prettyPrint(int depth) {
    array->prettyPrint(depth + 1);
    cout << "[";
    msb->prettyPrint(depth + 1);
    if (lsb) {
        cout << " : ";
        lsb->prettyPrint(depth + 1);
    }
    cout << "]";
}

shared_ptr<ArraySubExpr> ArraySubExpr::arraySubExpr() {
    return static_pointer_cast<ArraySubExpr, Expr>(shared_from_this());
}

shared_ptr<Expr> ArraySubExpr::rename(string prefix, LexicalScope &scope) {
    return shared_ptr<ArraySubExpr>(new ArraySubExpr(array->rename(prefix, scope),
                                                     msb->rename(prefix, scope),
                                                     lsb->rename(prefix, scope)));
}

StringConst::StringConst(const string &repr)
    : Expr(StringConstType), repr(repr) {

}

StringConst::~StringConst() {

}

void StringConst::prettyPrint(int depth) {
    cout << repr;
}

shared_ptr<StringConst> StringConst::stringConst() { return static_pointer_cast<StringConst, Expr>(shared_from_this()); }

shared_ptr<Expr> StringConst::rename(string prefix, LexicalScope &scope) {
    return shared_ptr<StringConst>(new StringConst(repr));
}