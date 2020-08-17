//
// Created by Jamey Hicks on 10/31/19.
//

#include <iostream>

#include "LValue.h"
#include "Stmt.h"

VarLValue::VarLValue(const string &name, const shared_ptr<BSVType> &bsvtype)
: LValue(VarLValueType), name(name), bsvtype(bsvtype) {
    attrs_.boundVars[name] = bsvtype;
    attrs_.freeVars[name] = bsvtype;
}

VarLValue::~VarLValue(){}

void VarLValue::prettyPrint(ostream &out, int depth) {
    cout << name << ": " << bsvtype->to_string();
}

shared_ptr<VarLValue> VarLValue::varLValue() {
    return static_pointer_cast<VarLValue, LValue>(shared_from_this());
}

shared_ptr<LValue> VarLValue::rename(string prefix, shared_ptr<LexicalScope> &scope)
{
    //FIXME:
    shared_ptr<Declaration> binding = scope->lookup(name);
    if (binding) {
        return make_shared<VarLValue>(binding->name, binding->bsvtype);
    } else {
        return make_shared<VarLValue>(name, binding->bsvtype);
    }
}

FieldLValue::FieldLValue(const shared_ptr<Expr> &obj, const string &field)
: LValue(FieldLValueType), obj(obj), field(field) {
    uniteSet(attrs_.assignedVars, obj->attrs().freeVars);

    uniteSet(attrs_.freeVars, obj->attrs().freeVars);
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
    uniteSet(attrs_.assignedVars, array->attrs().freeVars);

    uniteSet(attrs_.freeVars, array->attrs().freeVars);
    uniteSet(attrs_.freeVars, index->attrs().freeVars);
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
    uniteSet(attrs_.assignedVars, bitarray->attrs().freeVars);

    uniteSet(attrs_.freeVars, bitarray->attrs().freeVars);
    uniteSet(attrs_.freeVars, msb->attrs().freeVars);
    uniteSet(attrs_.freeVars, lsb->attrs().freeVars);

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
    return make_shared<RangeSelLValue>(bitarray->rename(prefix, scope), msb->rename(prefix, scope), lsb->rename(prefix, scope));
}

shared_ptr<RangeSelLValue> RangeSelLValue::rangeSelLValue() {
    return static_pointer_cast<RangeSelLValue, LValue>(shared_from_this());
}