
#pragma once

#include <map>
#include <memory>
#include <string>

using namespace std;

class Value {
 public:
  Value() {}
  virtual ~Value() {}
};

class ValueContext {
  map<string,shared_ptr<Value>> bindings;
  shared_ptr<ValueContext> parent;
 public:
  LexicalScope() {}
  LexicalScope(const shared_ptr<LexicalScope> &parent) : parent(parent) {}
  ~LexicalScope() {}

  shared_ptr<Value> lookup(const string &name) const;
  void bind(const string &name, const shared_ptr<Value> &value);
};

class IntValue : public Value {
 public:
  const long value;
  const int width;
  const string basespec;

  IntValue(long value, int width=0, const string &basespec)
    value(value), width(width), basespec(basespec) {
  }
  ~IntValue() override {}
};

class BoolValue : public Value {
 public:
  const bool value;

  BoolValue(bool value)
    value(value) {
  }
  ~BoolValue() override {}

};

class VectorValue : public Value {
 public:
 final vector<shared_ptr<Value>> values;
 final int size;
 VectorValue(long size) : values(size) {
        this.size = (int)size;
 }
 ~VectorValue() override {}
};

class RegValue : public Value {
 public:
  const string name;
  //FIXME bsvtype
  shared_ptr<Value> value;
  shared_ptr<Value> newValue;

  RegValue(const string &name, const shared_ptr<Value> &initialValue)
    : name(name), initialValue(initialValue) {
  }

  RegValue(const string &name)
    : name(name) {
  }
  ~RegValue() override {}

  void update(shared_ptr<Value> v) {
    newValue = v;
  }
  void commit() {
    value = newValue;
  }
};

class Rule : public Value {
 public:
    const string name;
    const shared_ptr<RuleStmt> ruleStmt;
    shared_ptr<ValueContext> context;

    Rule (const string &name, const shared_ptr<RuleStmt> &ruleStmt)
      : name(name), ruleStmt(ruleStmt) {
    }
    ~Rule() override {}
};

class ModuleInstance : public Value {
 public:
    const string name;
    const shared_ptr<ModuleDefStmt> module;
    shared_ptr<ValueContext> context;

    ModuleInstance(const string &name, const shared_ptr<ModuleDefStmt> &module)
      : name(name), module(module) {
    }

    ~ModuleInstance() override {}

};
