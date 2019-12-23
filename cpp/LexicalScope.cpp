
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

void LexicalScope::import(const shared_ptr<LexicalScope> &scope)
{
    for (auto it = scope->bindings.cbegin(); it != scope->bindings.cend(); ++it) {
        //FIXME only if no conflicts
        cerr << "Importing " << scope->name << "::" << it->first << endl;
        bind(it->first, it->second);
    }
}
