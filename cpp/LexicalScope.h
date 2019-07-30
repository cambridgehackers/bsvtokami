#pragma once

#include <map>
#include <memory>
#include <string>

using namespace std;

class LexicalScope {
  map<string,string> bindings;
  const LexicalScope *parent;
 public:
  LexicalScope() {}
  LexicalScope(const LexicalScope *parent) : parent(parent) {}
  ~LexicalScope() {}
  string lookup(const string &name) const;
  void bind(const string &name, const string &value);
};
