
#pragma once

#include <Expr.h>
#include <Stmt.h>
#include <Value.h>

class Elaborator {
 public:
  Elaborator() {
  }

  shared_ptr<Value> eval(const shared_ptr<Expr> &expr);
  shared_ptr<Value> eval(const shared_ptr<Stmt> &expr);

  shared_ptr<ModuleDefStmt> elaborate(const string &moduleName);

};
