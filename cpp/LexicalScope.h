#pragma once

#include <map>
#include <memory>
#include <string>

#include "Declaration.h"

using namespace std;

class LexicalScope {
    const string name;
    map<string, shared_ptr<Declaration>> bindings;
    vector<shared_ptr<Declaration>> bindingList;
public:
    LexicalScope(const string &name) : name(name), parent() {}
    LexicalScope(const string &name, shared_ptr<LexicalScope> &parent) : name(name), parent(parent) {}

    ~LexicalScope() {}

    bool isGlobal() { return parent == NULL; }

    shared_ptr<Declaration> lookup(const string &name) const;

    void bind(const string &name, const shared_ptr<Declaration> &value);
    void import(const shared_ptr<LexicalScope> &scope);
    void visit(DeclarationVisitor &visitor);

    shared_ptr<LexicalScope> parent;
};
