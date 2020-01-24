
#include "Inliner.h"

vector<shared_ptr<Stmt>> Inliner::processPackage(vector<shared_ptr<Stmt>> &packageStmts)
{
    vector<shared_ptr<Stmt>> processedStmts;
    for (size_t i = 0; i < packageStmts.size(); i++) {
        shared_ptr<Stmt> stmt = packageStmts[i];
        if (stmt->moduleDefStmt()) {
            shared_ptr<ModuleDefStmt> moduleDef = processModuleDef(stmt->moduleDefStmt());
            constructors[moduleDef->name] = moduleDef;
            stmt = moduleDef;
        }
        processedStmts.push_back(stmt);
    }
    return processedStmts;
}

shared_ptr<ModuleDefStmt> Inliner::processModuleDef(const shared_ptr<ModuleDefStmt> &moduleDef)
{
    vector<shared_ptr<Stmt>> stmts = moduleDef->stmts;
    vector<shared_ptr<Stmt>> inlinedStmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt = stmts[i];
        bool inlined = false;
        if (shared_ptr<ActionBindingStmt> actionBindingStmt = stmt->actionBindingStmt()) {
            string instanceName = actionBindingStmt->name;
            shared_ptr <Expr> rhs = actionBindingStmt->rhs;
            if (shared_ptr<CallExpr> callExpr = rhs->callExpr()) {
                if (shared_ptr<VarExpr> varExpr = callExpr->function->varExpr()) {
                    auto ct = constructors.find(varExpr->name);
                    if (ct != constructors.cend()) {
                        cerr << "inlining module " << instanceName << " constructor " << varExpr->name << endl;
                        shared_ptr<ModuleDefStmt> constructorDef = ct->second;
                        shared_ptr<LexicalScope> scope(make_shared<LexicalScope>(moduleDef->name));
                        string prefix;
                        shared_ptr<Stmt> renamedStmt = constructorDef->rename(varExpr->name + "$", scope);
                        constructorDef = renamedStmt->moduleDefStmt();
                        instances[instanceName] = constructorDef;
                        inlined = true;
                        vector<shared_ptr<Stmt>> constructorStmts = constructorDef->stmts;
                        for (size_t i = 0; i < constructorStmts.size(); i++) {
                            if (!constructorStmts[i]->methodDefStmt())
                                inlinedStmts.push_back(constructorStmts[i]);
                        }
                    }
                } else if (shared_ptr<FieldExpr> fieldExpr = callExpr->function->fieldExpr()) {
                    if (shared_ptr<VarExpr> varExpr = fieldExpr->object->varExpr()) {
                        auto it = instances.find(varExpr->name);
                        if (it != instances.cend()) {
                            cerr << "inlining method " << varExpr->name << endl;
                            //FIXME: inline method
                        }
                    }
                }
            }
        }
        if (!inlined)
            inlinedStmts.push_back(stmt);
    }
    return make_shared<ModuleDefStmt>(moduleDef->package, moduleDef->name, moduleDef->interfaceType, moduleDef->params, moduleDef->paramTypes, inlinedStmts);
}

vector<shared_ptr<Stmt>> Inliner::processStmt(const shared_ptr<Stmt> &stmt)
{
    vector<shared_ptr<Stmt>> inlinedStmts;
    if (shared_ptr<ActionBindingStmt> actionBindingStmt = stmt->actionBindingStmt()) {
            string instanceName = actionBindingStmt->name;
            shared_ptr <Expr> rhs = actionBindingStmt->rhs;
	    bool inlined = false;
            if (shared_ptr<CallExpr> callExpr = rhs->callExpr()) {
                if (shared_ptr<VarExpr> varExpr = callExpr->function->varExpr()) {
                    auto ct = constructors.find(varExpr->name);
                    if (ct != constructors.cend()) {
                        cerr << "inlining module " << instanceName << " constructor " << varExpr->name << endl;
                        shared_ptr<ModuleDefStmt> constructorDef = ct->second;
                        shared_ptr<LexicalScope> scope(make_shared<LexicalScope>(constructorDef->name));
                        string prefix;
                        shared_ptr<Stmt> renamedStmt = constructorDef->rename(varExpr->name + "$", scope);
                        constructorDef = renamedStmt->moduleDefStmt();
                        instances[instanceName] = constructorDef;
                        inlined = true;
                        vector<shared_ptr<Stmt>> constructorStmts = constructorDef->stmts;
                        for (size_t i = 0; i < constructorStmts.size(); i++) {
                            if (!constructorStmts[i]->methodDefStmt())
                                inlinedStmts.push_back(constructorStmts[i]);
                        }
                    }
                } else if (shared_ptr<FieldExpr> fieldExpr = callExpr->function->fieldExpr()) {
                    if (shared_ptr<VarExpr> varExpr = fieldExpr->object->varExpr()) {
                        auto it = instances.find(varExpr->name);
                        if (it != instances.cend()) {
                            cerr << "inlining method " << varExpr->name << endl;
                            //FIXME: inline method
                        }
                    }
                }
            }
	    if (!inlined)
	      inlinedStmts.push_back(stmt);
    }
    return inlinedStmts;
}
