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

void VarLValue::prettyPrint(ostream &out, int depth) {
    cout << name;
}

shared_ptr<VarLValue> VarLValue::varLValue() {
    return static_pointer_cast<VarLValue, LValue>(shared_from_this());
}

shared_ptr<struct LValue> VarLValue::rename(string prefix, shared_ptr<LexicalScope> &scope)
{
    //FIXME:
    shared_ptr<Declaration> binding = scope->lookup(name);
    if (binding) {
        return shared_ptr<struct LValue>(new VarLValue(binding->name));
    } else {
        return shared_ptr<struct LValue>(new VarLValue(name));
    }
}

FieldLValue::FieldLValue(const shared_ptr<Expr> &obj, const string &field)
: LValue(FieldLValueType), obj(obj), field(field) {

}

FieldLValue::~FieldLValue() {}
void FieldLValue::prettyPrint(ostream &out, int depth) {
    obj->prettyPrint(out, depth);
    cout << "." << field;
}

shared_ptr<FieldLValue> FieldLValue::fieldLValue() {
    return static_pointer_cast<FieldLValue, LValue>(shared_from_this());
}

shared_ptr<struct LValue> FieldLValue::rename(string prefix, shared_ptr<LexicalScope> &scope)
{
    return shared_ptr<LValue>(new FieldLValue(obj->rename(prefix, scope), field));
}

shared_ptr<LValue> FieldLValue::create(shared_ptr<Expr> obj, string fieldname) {
    return shared_ptr<LValue>(new FieldLValue(obj, fieldname));
}

ArraySubLValue::ArraySubLValue(const shared_ptr<Expr> &array, const shared_ptr<Expr> &index)
: LValue(ArraySubLValueType), array(array), index(index) {

}

ArraySubLValue::~ArraySubLValue() {

}

void ArraySubLValue::prettyPrint(ostream &out, int depth) {
    array->prettyPrint(out, depth);
    cout << "[";
    index->prettyPrint(out, depth);
    cout << "]";
}

shared_ptr<ArraySubLValue> ArraySubLValue::arraySubLValue() {
    return static_pointer_cast<ArraySubLValue, LValue>(shared_from_this());
}

shared_ptr<struct LValue> ArraySubLValue::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    return create(array->rename(prefix, scope), index->rename(prefix, scope));
}

shared_ptr<LValue> ArraySubLValue::create(shared_ptr<Expr> array, const shared_ptr<Expr> &index) {
    return shared_ptr<LValue>(new ArraySubLValue(array, index));
}

RangeSelLValue::RangeSelLValue(const shared_ptr<Expr> &bitarray, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb)
: LValue(RangeSelLValueType), bitarray(bitarray), msb(msb), lsb(lsb) {

}

RangeSelLValue::~RangeSelLValue(){}

void RangeSelLValue::prettyPrint(ostream &out, int depth) {
    bitarray->prettyPrint(out, depth);
    cout << "[";
    msb->prettyPrint(out, depth);
    cout << " : ";
    lsb->prettyPrint(out, depth);
    cout << "]";
}

shared_ptr<struct LValue> RangeSelLValue::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    return create(bitarray->rename(prefix, scope), msb->rename(prefix, scope), lsb->rename(prefix, scope));
}

shared_ptr<LValue> RangeSelLValue::create(shared_ptr<Expr> bitarray, const shared_ptr<Expr> &msb, const shared_ptr<Expr> &lsb) {
    return shared_ptr<LValue>(new RangeSelLValue(bitarray, msb, lsb));
}