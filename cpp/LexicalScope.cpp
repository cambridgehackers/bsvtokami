
#include "LexicalScope.h"

shared_ptr<Declaration> LexicalScope::lookup(const string &name) const {
    auto it = bindings.find(name);
    if (it != bindings.end()) {
        shared_ptr<Declaration> value = it->second;
        return value;
    } else if (parent) {
        return parent->lookup(name);
    } else {
        return shared_ptr<Declaration>();
    }
}

void LexicalScope::bind(const string &name, const shared_ptr<Declaration> &value) {
    bindings[name] = value;
}
