
#include "LexicalScope.h"

string LexicalScope::lookup(const string &name) const {
    auto it = bindings.find(name);
    if (it != bindings.end()) {
        string value = it->second;
        return value;
    } else if (parent) {
        return parent->lookup(name);
    } else {
        return string();
    }
}

void LexicalScope::bind(const string &name, const string &value) {
    bindings[name] = value;
}
