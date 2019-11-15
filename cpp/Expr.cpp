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
    prettyPrint(cout, 4);
    return shared_ptr<Expr>();
}

VarExpr::VarExpr(const string &name, const shared_ptr<BSVType> &bsvtype)
        : Expr(VarExprType), name(name), sourceName(name), bsvtype(bsvtype) {
}

VarExpr::~VarExpr() {
}

void VarExpr::prettyPrint(ostream &out, int depth) {
    out << name << "(* : ";
    bsvtype->prettyPrint(out, depth);
    out << " *)";
}

shared_ptr<VarExpr> VarExpr::varExpr() { return static_pointer_cast<VarExpr, Expr>(shared_from_this()); }

shared_ptr<Expr> VarExpr::rename(string prefix, LexicalScope &scope) {
    string renamed = scope.lookup(name);
    if (!renamed.size())
        renamed = name;
    return shared_ptr<VarExpr>(new VarExpr(renamed, bsvtype));
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

void IntConst::prettyPrint(ostream &out, int depth) {
    out << repr;
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

void OperatorExpr::prettyPrint(ostream &out, int depth) {
    if (!rhs) {
        out << op << " ";
    }
    lhs->prettyPrint(out, depth + 1);
    if (rhs) {
        out << " " << op << " ";
        rhs->prettyPrint(out, depth + 1);
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

MatchesExpr::MatchesExpr(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern)
        : Expr(MatchesExprType), expr(expr), pattern(pattern) {
}

MatchesExpr::MatchesExpr(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern, const vector<shared_ptr<Expr>> &patterncond)
    : Expr(MatchesExprType), expr(expr), pattern(pattern), patterncond(patterncond) {

}

MatchesExpr::~MatchesExpr() {

}

void MatchesExpr::prettyPrint(ostream &out, int depth) {
    expr->prettyPrint(out, depth);
    out << " matches ";
    //fixme: string
    out << pattern;
    for (int i = 0; i < patterncond.size(); i++) {
        out << " &&& ";
        patterncond[i]->prettyPrint(out, depth);
    }
};

shared_ptr<MatchesExpr> MatchesExpr::matchesExpr() {
    return static_pointer_cast<MatchesExpr, Expr>(shared_from_this());
}

shared_ptr<Expr> MatchesExpr::rename(string prefix, LexicalScope &renames) {
    //FIXME: implement
    return MatchesExpr::create(expr, pattern, patterncond);
}

shared_ptr<MatchesExpr> MatchesExpr::create(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern) {
    return shared_ptr<MatchesExpr>(new MatchesExpr(expr, pattern));
}

shared_ptr<MatchesExpr> MatchesExpr::create(const shared_ptr<Expr> &expr, const shared_ptr<Pattern> &pattern,
                                      const vector<shared_ptr<Expr>> &exprs) {
    return shared_ptr<MatchesExpr>(new MatchesExpr(expr, pattern, exprs));
}

FieldExpr::FieldExpr(const shared_ptr<Expr> &object, const std::string &fieldName)
        : Expr(FieldExprType), object(object), fieldName(fieldName) {
}

FieldExpr::~FieldExpr() {

}

void FieldExpr::prettyPrint(ostream &out, int depth) {
    object->prettyPrint(out, depth + 1);
    out << "." << fieldName;
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

void CallExpr::prettyPrint(ostream &out, int depth) {
    function->prettyPrint(out, depth + 1);
    out << "(";
    for (size_t i = 0; i < args.size(); i++) {
        if (i > 0)
            out << ", ";
        if (args[i])
            args[i]->prettyPrint(out, depth + 1);
        else
            out << "emptyarg:" << to_string(i);
    }
    out << ")";
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

void EnumUnionStructExpr::prettyPrint(ostream &out, int depth) {
    out << tag << " {";
    for (size_t i = 0; i < keys.size(); i++) {
        if (i > 0)
            out << ";";
        out << " " << keys.at(i) << ": ";
        vals.at(i)->prettyPrint(out, depth + 1);
    }
    out << " }";
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

void ArraySubExpr::prettyPrint(ostream &out, int depth) {
    array->prettyPrint(out, depth + 1);
    out << "[";
    msb->prettyPrint(out, depth + 1);
    if (lsb) {
        out << " : ";
        lsb->prettyPrint(out, depth + 1);
    }
    out << "]";
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

void StringConst::prettyPrint(ostream &out, int depth) {
    out << repr;
}

shared_ptr<StringConst> StringConst::stringConst() { return static_pointer_cast<StringConst, Expr>(shared_from_this()); }

shared_ptr<Expr> StringConst::rename(string prefix, LexicalScope &scope) {
    return shared_ptr<StringConst>(new StringConst(repr));
}

CondExpr::CondExpr(const shared_ptr<Expr> &cond, const shared_ptr<Expr> &thenExpr, const shared_ptr<Expr> &elseExpr)
    : Expr(CondExprType), cond(cond), thenExpr(thenExpr), elseExpr(elseExpr) {

}

CondExpr::~CondExpr() {

}

void CondExpr::prettyPrint(ostream &out, int depth) {
    out << "(";
    cond->prettyPrint(out, depth);
    out << ") ? (";
    thenExpr->prettyPrint(out, depth);
    out << ") : (";
    elseExpr->prettyPrint(out, depth);
    out << ")";
}

shared_ptr<CondExpr> CondExpr::condExpr() {
    return static_pointer_cast<CondExpr, Expr>(shared_from_this());
}

shared_ptr<Expr> CondExpr::rename(string prefix, LexicalScope &renames) {
    return shared_ptr<CondExpr>(new CondExpr(cond->rename(prefix, renames),
                                             thenExpr->rename(prefix, renames),
                                             elseExpr->rename(prefix, renames)));
}

