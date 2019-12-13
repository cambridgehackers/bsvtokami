#pragma once

#include <map>
#include <memory>
#include <string>

#include "Declaration.h"

using namespace std;

class LexicalScope {
    map<string, shared_ptr<Declaration>> bindings;
public:
    LexicalScope(LexicalScope *parent = nullptr) : parent(parent) {}

    ~LexicalScope() {}

    bool isGlobal() { return parent == NULL; }

    shared_ptr<Declaration> lookup(const string &name) const;

    void bind(const string &name, const shared_ptr<Declaration> &value);

    LexicalScope *parent;
};
