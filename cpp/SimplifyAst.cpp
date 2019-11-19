//
// Created by Jamey Hicks on 11/13/19.
//

#include "SimplifyAst.h"

void
SimplifyAst::simplify(const vector<shared_ptr<struct Stmt>> &stmts, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    cerr << "simplify stmts" << endl;
    for (int i = 0; i < stmts.size(); i++) {
        simplify(stmts[i], simplifiedStmts);
    }
}

void SimplifyAst::simplify(const shared_ptr<struct Stmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    switch (stmt->stmtType) {
        case InvalidStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case ActionBindingStmtType:
            simplify(stmt->actionBindingStmt(), simplifiedStmts);
            return;
        case BlockStmtType:
            simplify(stmt->blockStmt(), simplifiedStmts);
            return;
        case CallStmtType:
            simplify(stmt->callStmt(), simplifiedStmts);
            return;
        case ExprStmtType:
            simplify(stmt->exprStmt(), simplifiedStmts);
            return;
        case FunctionDefStmtType:
            simplify(stmt->functionDefStmt(), simplifiedStmts);
            return;
        case InterfaceDeclStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case InterfaceDefStmtType:
            simplify(stmt->interfaceDefStmt(), simplifiedStmts);
            return;
        case IfStmtType:
            simplify(stmt->ifStmt(), simplifiedStmts);
            return;
        case ImportStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case MethodDeclStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case MethodDefStmtType:
            simplify(stmt->methodDefStmt(), simplifiedStmts);
            return;
        case ModuleDefStmtType:
            simplify(stmt->moduleDefStmt(), simplifiedStmts);
            return;
        case ModuleInstStmtType:
            simplify(stmt->moduleInstStmt(), simplifiedStmts);
            return;
        case PackageDefStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case RegReadStmtType:
            simplify(stmt->regReadStmt(), simplifiedStmts);
            return;
        case RegWriteStmtType:
            simplify(stmt->regWriteStmt(), simplifiedStmts);
            return;
        case ReturnStmtType:
            simplify(stmt->returnStmt(), simplifiedStmts);
            return;
        case TypedefStructStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case TypedefSynonymStmtType:
            simplifiedStmts.push_back(stmt);
            return;
        case VarBindingStmtType:
            simplify(stmt->varBindingStmt(), simplifiedStmts);
            return;
        case VarAssignStmtType:
            simplify(stmt->varAssignStmt(), simplifiedStmts);
            return;
        case RuleDefStmtType:
            simplify(stmt->ruleDefStmt(), simplifiedStmts);
            return;
    }
}

void
SimplifyAst::simplify(const shared_ptr<ActionBindingStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    if (!actionContext) {
        //FIXME: maybe this should be done in GenerateAst
        shared_ptr<BSVType> bsvtype = stmt->bsvtype;
        if (bsvtype->name == "Reg") {
            string regname = stmt->name;
            cerr << "regname " << regname << endl;
            registers[regname] = bsvtype->params[0];
        }
    }
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<BlockStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    for (int i = 0; i < stmt->stmts.size(); i++) {
        simplify(stmt->stmts[i], simplifiedStmts);
    }
    shared_ptr<Stmt> newblockstmt(new BlockStmt(simplifiedStmts));
    cerr << "simplified block stmt" << endl;
    simplifiedStmts.push_back(newblockstmt);
}

void SimplifyAst::simplify(const shared_ptr<ExprStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<IfStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<ImportStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void
SimplifyAst::simplify(const shared_ptr<InterfaceDeclStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<MethodDeclStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<MethodDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void
SimplifyAst::simplify(const shared_ptr<ModuleDefStmt> &moduleDef, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    registers.clear();
    vector<shared_ptr<Stmt>> simplifiedModuleStmts;
    simplify(moduleDef->stmts, simplifiedModuleStmts);
    shared_ptr<Stmt> newModuleDef(new ModuleDefStmt(moduleDef->name, moduleDef->interfaceType,
                                                    moduleDef->params, moduleDef->paramTypes, simplifiedModuleStmts));
    cerr << "simplify moduledef " << moduleDef->name << endl;
    newModuleDef->prettyPrint(cerr, 0);
    cerr << endl;
    simplifiedStmts.push_back(newModuleDef);
}

void SimplifyAst::simplify(const shared_ptr<RegReadStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<RegWriteStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    cerr << "simplify regwrite stmt " << stmt->regName << endl;
    shared_ptr<Expr> simplifiedRhs = simplify(stmt->rhs, simplifiedStmts);
    simplifiedStmts.push_back(make_shared<RegWriteStmt>(stmt->regName, simplifiedRhs));
}

void SimplifyAst::simplify(const shared_ptr<ReturnStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    shared_ptr<Expr> simplifiedExpr = simplify(stmt->value, simplifiedStmts);
    simplifiedStmts.push_back(make_shared<ReturnStmt>(simplifiedExpr));
}

void SimplifyAst::simplify(const shared_ptr<RuleDefStmt> &ruleDef, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    vector<shared_ptr<Stmt>> ruleSimplifiedStmts;
    simplify(ruleDef->stmts, ruleSimplifiedStmts);
    shared_ptr<RuleDefStmt> newRuleDef = make_shared<RuleDefStmt>(ruleDef->name, ruleDef->guard, ruleSimplifiedStmts);
    simplifiedStmts.push_back(newRuleDef);
}

void
SimplifyAst::simplify(const shared_ptr<TypedefStructStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void
SimplifyAst::simplify(const shared_ptr<TypedefSynonymStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<VarBindingStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

shared_ptr<Expr> SimplifyAst::simplify(const shared_ptr<Expr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    switch (expr->exprType) {
        case InvalidExprType:
            return expr;
        case ArraySubExprType: {
            shared_ptr<ArraySubExpr> opexpr = expr->arraySubExpr();
            shared_ptr<Expr> array = simplify(opexpr->array, simplifiedStmts);
            shared_ptr<Expr> msb = simplify(opexpr->msb, simplifiedStmts);
            shared_ptr<Expr> lsb = simplify(opexpr->lsb, simplifiedStmts);
            shared_ptr<ArraySubExpr> simplifiedExpr = make_shared<ArraySubExpr>(array, msb, lsb);
            return simplifiedExpr;
        }
        case VarExprType: {
            shared_ptr<VarExpr> varExpr = expr->varExpr();
            if (registers.find(varExpr->name) != registers.cend()) {
                shared_ptr<BSVType> elementType = registers.find(varExpr->name)->second;
                cerr << "simplify var expr reading reg " << varExpr->name << endl;
                string valName = varExpr->name + "$val";
                shared_ptr<RegReadStmt> regRead = make_shared<RegReadStmt>(varExpr->name, valName, elementType);
                simplifiedStmts.push_back(regRead);
                return make_shared<VarExpr>(valName, elementType);
            }
        }
            break;
        case IntConstType:
        case StringConstType:
            return expr;
        case OperatorExprType: {
            shared_ptr<OperatorExpr> opexpr = expr->operatorExpr();
            shared_ptr<Expr> lhs = simplify(opexpr->lhs, simplifiedStmts);
            shared_ptr<Expr> rhs = simplify(opexpr->rhs, simplifiedStmts);
            shared_ptr<OperatorExpr> simplifiedExpr = make_shared<OperatorExpr>(opexpr->op, lhs, rhs);
            return simplifiedExpr;
        }
        case CallExprType: {
            cerr << "FIXME: simplify call expr: ";
            expr->prettyPrint(cerr, 0);
            cerr << endl;
            return expr;
        }
        case FieldExprType: {
            shared_ptr<FieldExpr> fieldExpr = expr->fieldExpr();
            shared_ptr<Expr> object = simplify(fieldExpr->object, simplifiedStmts);
            shared_ptr<FieldExpr> simplifiedExpr = make_shared<FieldExpr>(object, fieldExpr->fieldName);
            return simplifiedExpr;
        }
        case CondExprType: {
            shared_ptr<CondExpr> condExpr = expr->condExpr();
            shared_ptr<Expr> cond = simplify(condExpr->cond, simplifiedStmts);
            shared_ptr<Expr> thenExpr = simplify(condExpr->thenExpr, simplifiedStmts);
            shared_ptr<Expr> elseExpr = simplify(condExpr->elseExpr, simplifiedStmts);
            shared_ptr<CondExpr> simplifiedExpr = make_shared<CondExpr>(cond, thenExpr, elseExpr);
            return simplifiedExpr;
        }
        case CaseExprType:
            //FIXME case expr
            return expr;
        case EnumUnionStructExprType:
        case MatchesExprType:
            cerr << "FIXME: simplify expr: " << endl;
            expr->prettyPrint(cerr, 0);
            cerr << endl;
            return expr;
    }
    return expr;
}
