//
// Created by Jamey Hicks on 10/31/19.
//

#include <iostream>

#include "LValue.h"

VarLValue::VarLValue(const string &name)
: LValue(VarLValueType), name(name) {
}

shared_ptr<VarLValue> VarLValue::create(const string &name) {
    return shared_ptr<VarLValue>(new VarLValue(name));
}

VarLValue::~VarLValue(){}

void VarLValue::prettyPrint(int depth) {
    cout << name;
}

shared_ptr<struct LValue> VarLValue::rename(string prefix, LexicalScope &scope)
{
    //FIXME:
    string binding = scope.lookup(name);
    if (binding.size()) {
        return shared_ptr<struct LValue>(new VarLValue(binding));
    } else {
        return shared_ptr<struct LValue>(new VarLValue(name));
    }
}

FieldLValue::FieldLValue(const shared_ptr<LValue> &lhs, const string &field)
: LValue(FieldLValueType), lhs(lhs), field(field) {

}

FieldLValue::~FieldLValue() {}
void FieldLValue::prettyPrint(int depth) {
    lhs->prettyPrint(depth);
    cout << "." << field;
}

shared_ptr<struct LValue> FieldLValue::rename(string prefix, LexicalScope &scope)
{
    return shared_ptr<LValue>(new FieldLValue(lhs->rename(prefix, scope), field));
}

shared_ptr<LValue> FieldLValue::create(shared_ptr<LValue> lhs, string fieldname) {
    return shared_ptr<LValue>(new FieldLValue(lhs, fieldname));
}

ArraySubLValue::ArraySubLValue(const shared_ptr<LValue> &lhs, const shared_ptr<Expr> &index)
: LValue(ArraySubLValueType), lhs(lhs), index(index) {

}

ArraySubLValue::~ArraySubLValue() {

}

void ArraySubLValue::prettyPrint(int depth) {
    lhs->prettyPrint(depth);
    cout << "[";
    index->prettyPrint(depth);
    cout << "]";
}

shared_ptr<struct LValue> ArraySubLValue::rename(string prefix, LexicalScope &scope) {
    return create(lhs->rename(prefix, scope), index->rename(prefix, scope));
}

shared_ptr<LValue> ArraySubLValue::create(shared_ptr<LValue> lhs, const shared_ptr<Expr> &index) {
    return shared_ptr<LValue>(new ArraySubLValue(lhs, index));
}

RangeSelLValue::RangeSelLValue(const shared_ptr<LValue> &lhs, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb)
: LValue(RangeSelLValueType), lhs(lhs), msb(msb), lsb(lsb) {

}

RangeSelLValue::~RangeSelLValue(){}

void RangeSelLValue::prettyPrint(int depth) {
    lhs->prettyPrint(depth);
    cout << "[";
    msb->prettyPrint(depth);
    cout << " : ";
    lsb->prettyPrint(depth);
    cout << "]";
}

shared_ptr<struct LValue> RangeSelLValue::rename(string prefix, LexicalScope &scope) {
    return create(lhs->rename(prefix, scope), msb->rename(prefix, scope), lsb->rename(prefix, scope));
}

shared_ptr<LValue> RangeSelLValue::create(shared_ptr<LValue> lhs, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb) {
    return shared_ptr<LValue>(new RangeSelLValue(lhs, msb, lsb));
}