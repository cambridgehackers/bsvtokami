
#pragma once

#include <map>
#include <memory>
#include <string>

#include "Stmt.h"

using namespace std;

class Inliner {
  map<string,shared_ptr<ModuleDefStmt>> constructors;
  map<string,shared_ptr<ModuleDefStmt>> instances;
 public:
  Inliner() {}
  ~Inliner() {}

  vector<shared_ptr<Stmt>> processPackage(vector<shared_ptr<Stmt>> &packageStmts);
  shared_ptr<ModuleDefStmt> processModuleDef(const shared_ptr<ModuleDefStmt> &moduleDef);
  vector<shared_ptr<Stmt>> processStmt(const shared_ptr<Stmt> &stmt);

};
