//
// Created by Jamey Hicks on 11/13/19.
//

#include "SimplifyAst.h"

void
SimplifyAst::simplify(const vector<shared_ptr<struct Stmt>> &stmts, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    //logstream << "simplify stmts" << endl;
    for (int i = 0; i < stmts.size(); i++) {
        if (!stmts[i]) {
            cerr << "Null stmt number " << i << " of " << stmts.size() << " at " << stmts[i - 1]->sourcePos.toString()
                 << endl;
            stmts[i - 1]->prettyPrint(cerr);
            cerr << endl;
        }
        simplify(stmts[i], simplifiedStmts);
    }
}

shared_ptr<struct Stmt> SimplifyAst::simplifySubstatement(const shared_ptr<struct Stmt> &stmt) {
    if (!stmt)
        return stmt;

    vector<shared_ptr<struct Stmt>> simplifiedStmts;
    simplify(stmt, simplifiedStmts);
    assert(simplifiedStmts.size() > 0);
    if (simplifiedStmts.size() > 1) {
        return make_shared<BlockStmt>(simplifiedStmts, stmt->sourcePos);
    } else {
        return simplifiedStmts[0];
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
        case PatternMatchStmtType:
            simplify(stmt->patternMatchStmt(), simplifiedStmts);
            return;
        case RegisterStmtType:
            simplify(stmt->registerStmt(), simplifiedStmts);
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
            logstream << "regname " << regname << endl;
            registers[regname] = bsvtype->params[0];
        }
    }
    shared_ptr<Expr> expr = stmt->rhs;
    if (actionContext) {
        switch (expr->exprType) {
            case CallExprType: {
                simplifiedStmts.push_back(make_shared<CallStmt>(stmt->name, stmt->bsvtype, stmt->rhs, stmt->sourcePos));
            }
                break;
            case VarExprType:
            case FieldExprType: {
                vector<shared_ptr<Expr>> args;
                simplifiedStmts.push_back(make_shared<CallStmt>(stmt->name, stmt->bsvtype,
                                                                make_shared<CallExpr>(stmt->rhs, args),
                                                                stmt->sourcePos));
            }
                break;
            default:
                simplifiedStmts.push_back(stmt);
        }
    } else {
        switch (expr->exprType) {
            case CallExprType: {
                if (stmt->bsvtype->name == "Reg") {
                    shared_ptr<BSVType> elementType = stmt->bsvtype->params[0];
                    simplifiedStmts.push_back(make_shared<RegisterStmt>(stmt->name, elementType, stmt->sourcePos));
                } else {
                    simplifiedStmts.push_back(
                            make_shared<CallStmt>(stmt->name, stmt->bsvtype, stmt->rhs, stmt->sourcePos));
                }
            }
                break;
            case VarExprType: {
                if (stmt->bsvtype->name == "Reg") {
                    shared_ptr<BSVType> elementType = stmt->bsvtype->params[0];
                    simplifiedStmts.push_back(make_shared<RegisterStmt>(stmt->name, elementType, stmt->sourcePos));
                } else {
                    vector<shared_ptr<Expr>> args;
                    simplifiedStmts.push_back(make_shared<CallStmt>(stmt->name, stmt->bsvtype,
                                                                    make_shared<CallExpr>(stmt->rhs, args),
                                                                    stmt->sourcePos));
                }
            }
                break;
            default:
                simplifiedStmts.push_back(stmt);
        }
    }
}

void SimplifyAst::simplify(const shared_ptr<BlockStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    for (int i = 0; i < stmt->stmts.size(); i++) {
        simplify(stmt->stmts[i], simplifiedStmts);
    }
    shared_ptr<Stmt> newblockstmt = make_shared<BlockStmt>(simplifiedStmts, stmt->sourcePos);
    logstream << "simplified block stmt" << endl;
    simplifiedStmts.push_back(newblockstmt);
}

void SimplifyAst::simplify(const shared_ptr<ExprStmt> &exprStmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    shared_ptr<Expr> expr = exprStmt->expr;
    switch (expr->exprType) {
        case CallExprType: {
            simplifiedStmts.push_back(
                    make_shared<CallStmt>("unused", make_shared<BSVType>("Void"), expr, exprStmt->sourcePos));
        }
            break;
        case FieldExprType: // fall through
        case VarExprType: {
            vector<shared_ptr<Expr>> args;
            simplifiedStmts.push_back(make_shared<CallStmt>("unused", make_shared<BSVType>("Void"),
                                                            make_shared<CallExpr>(expr, args),
                                                            exprStmt->sourcePos));
        }
            break;
        default:
            logstream << "Unhandled expr stmt: " << expr->exprType << "{" << endl;
            expr->prettyPrint(logstream);
            logstream << "}" << endl;
            simplifiedStmts.push_back(exprStmt);
    }
}

void SimplifyAst::simplify(const shared_ptr<FunctionDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    bool enclosingActionContext = actionContext;
    actionContext = true;

    simplifiedStmts.push_back(stmt);

    actionContext = enclosingActionContext;
}

void SimplifyAst::simplify(const shared_ptr<IfStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(make_shared<IfStmt>(simplify(stmt->condition, simplifiedStmts),
                                                  simplifySubstatement(stmt->thenStmt),
                                                  simplifySubstatement(stmt->elseStmt),
                                                  stmt->sourcePos));
}

void SimplifyAst::simplify(const shared_ptr<ImportStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void
SimplifyAst::simplify(const shared_ptr<InterfaceDeclStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void
SimplifyAst::simplify(const shared_ptr<InterfaceDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<MethodDeclStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<MethodDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    bool enclosingActionContext = actionContext;
    actionContext = true;

    vector<shared_ptr<struct Stmt>> methodStmts;
    simplify(stmt->stmts, methodStmts);
    simplifiedStmts.push_back(make_shared<MethodDefStmt>(stmt->name,
                                                         stmt->returnType,
                                                         stmt->params,
                                                         stmt->paramTypes,
                                                         stmt->guard, //FIXME: simplify guard
                                                         methodStmts,
                                                         stmt->sourcePos
    ));

    actionContext = enclosingActionContext;
}

void
SimplifyAst::simplify(const shared_ptr<ModuleDefStmt> &moduleDef, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    registers.clear();
    vector<shared_ptr<Stmt>> simplifiedModuleStmts;
    simplify(moduleDef->stmts, simplifiedModuleStmts);
    shared_ptr<Stmt> newModuleDef = make_shared<ModuleDefStmt>(moduleDef->name, moduleDef->interfaceType,
                                                               moduleDef->params, moduleDef->paramTypes,
                                                               simplifiedModuleStmts,
                                                               moduleDef->sourcePos);
    logstream << "simplify moduledef " << moduleDef->name << endl;
    newModuleDef->prettyPrint(logstream, 0);
    logstream << endl;
    simplifiedStmts.push_back(newModuleDef);
}

void SimplifyAst::simplify(const shared_ptr<PatternMatchStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    //FIXME: replace with VarBindingStmt, etc
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<RegReadStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    // no simplification needed
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<RegWriteStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    //logstream << "simplify regwrite stmt " << stmt->regName << endl;
    shared_ptr<Expr> simplifiedRhs = simplify(stmt->rhs, simplifiedStmts);
    simplifiedStmts.push_back(
            make_shared<RegWriteStmt>(stmt->regName, stmt->elementType, simplifiedRhs, stmt->sourcePos));
}

void SimplifyAst::simplify(const shared_ptr<ReturnStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    shared_ptr<Expr> simplifiedExpr = simplify(stmt->value, simplifiedStmts);
    simplifiedStmts.push_back(make_shared<ReturnStmt>(simplifiedExpr, stmt->sourcePos));
}

void SimplifyAst::simplify(const shared_ptr<RuleDefStmt> &ruleDef, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    bool enclosingActionContext = actionContext;
    actionContext = true;

    vector<shared_ptr<Stmt>> ruleSimplifiedStmts;
    simplify(ruleDef->stmts, ruleSimplifiedStmts);
    shared_ptr<RuleDefStmt> newRuleDef = make_shared<RuleDefStmt>(ruleDef->name, ruleDef->guard, ruleSimplifiedStmts,
                                                                  ruleDef->sourcePos);
    simplifiedStmts.push_back(newRuleDef);

    actionContext = enclosingActionContext;
}

void
SimplifyAst::simplify(const shared_ptr<TypedefStructStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void
SimplifyAst::simplify(const shared_ptr<TypedefSynonymStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    simplifiedStmts.push_back(stmt);
}

void SimplifyAst::simplify(const shared_ptr<VarAssignStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    shared_ptr<LValue> lhs = stmt->lhs;
    shared_ptr<Expr> simplifiedRhs = simplify(stmt->rhs, simplifiedStmts);
    simplifiedStmts.push_back(make_shared<VarAssignStmt>(lhs, stmt->op, simplifiedRhs, stmt->sourcePos));
}

void SimplifyAst::simplify(const shared_ptr<VarBindingStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    shared_ptr<Expr> simplifiedRhs = simplify(stmt->rhs, simplifiedStmts);
    simplifiedStmts.push_back(make_shared<VarBindingStmt>(stmt->bsvtype, stmt->name, simplifiedRhs, stmt->sourcePos));
}

shared_ptr<Expr> SimplifyAst::simplify(const shared_ptr<Expr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    switch (expr->exprType) {
        case InvalidExprType:
            return expr;
        case ArraySubExprType: {
            shared_ptr<ArraySubExpr> arraysubexpr = expr->arraySubExpr();
            shared_ptr<Expr> value = simplify(arraysubexpr->array, simplifiedStmts);
            shared_ptr<Expr> index = simplify(arraysubexpr->index, simplifiedStmts);
            shared_ptr<ArraySubExpr> simplifiedExpr = make_shared<ArraySubExpr>(value, index, arraysubexpr->sourcePos);
            return simplifiedExpr;
        }
        case BitSelExprType: {
            shared_ptr<BitSelExpr> bitselexpr = expr->bitSelExpr();
            shared_ptr<Expr> array = simplify(bitselexpr->value, simplifiedStmts);
            shared_ptr<Expr> msb = simplify(bitselexpr->msb, simplifiedStmts);
            shared_ptr<Expr> lsb = simplify(bitselexpr->lsb, simplifiedStmts);
            shared_ptr<BitSelExpr> simplifiedExpr = make_shared<BitSelExpr>(array, msb, lsb, bitselexpr->sourcePos);
            return simplifiedExpr;
        }
        case BitConcatExprType: {
            shared_ptr<BitConcatExpr> bitconcatexpr = expr->bitConcatExpr();
            vector<shared_ptr<Expr>> simplifiedExprs;
            for (int i = 0; i < bitconcatexpr->values.size(); i++) {
                simplifiedExprs.push_back(simplify(bitconcatexpr->values[i], simplifiedStmts));
            }
            shared_ptr<BitConcatExpr> simplifiedExpr = make_shared<BitConcatExpr>(simplifiedExprs, bitconcatexpr->bsvtype, bitconcatexpr->sourcePos);
            return simplifiedExpr;
        }
        case VarExprType: {
            shared_ptr<VarExpr> varExpr = expr->varExpr();
            if (registers.find(varExpr->name) != registers.cend()) {
                shared_ptr<BSVType> elementType = registers.find(varExpr->name)->second;
                logstream << "simplify var expr reading reg " << varExpr->name << endl;
                string valName = varExpr->name + "_val";
                //fixme: no source pos
                shared_ptr<RegReadStmt> regRead = make_shared<RegReadStmt>(varExpr->name, valName, elementType, varExpr->sourcePos);
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
            shared_ptr<Expr> rhs;
            if (!lhs) {
                logstream << "null lhs after simplify ";
                opexpr->lhs->prettyPrint(logstream);
                logstream << endl;
            }
            if (opexpr->rhs) {
                rhs = simplify(opexpr->rhs, simplifiedStmts);
                if (!rhs) {
                    logstream << "null rhs after simplify ";
                    opexpr->rhs->prettyPrint(logstream);
                    logstream << endl;
                }
            }
            shared_ptr<OperatorExpr> simplifiedExpr = make_shared<OperatorExpr>(opexpr->op, lhs, rhs, opexpr->sourcePos);
            return simplifiedExpr;
        }
        case CallExprType: {
            logstream << "FIXME: simplify call expr: ";
            expr->prettyPrint(logstream, 0);
            logstream << endl;
            return expr;
        }
        case FieldExprType: {
            shared_ptr<FieldExpr> fieldExpr = expr->fieldExpr();
            shared_ptr<Expr> object = simplify(fieldExpr->object, simplifiedStmts);
            shared_ptr<FieldExpr> simplifiedExpr = make_shared<FieldExpr>(object, fieldExpr->fieldName,
                                                                          fieldExpr->bsvtype, fieldExpr->sourcePos);
            return simplifiedExpr;
        }
        case CondExprType: {
            shared_ptr<CondExpr> condExpr = expr->condExpr();
            shared_ptr<Expr> cond = simplify(condExpr->cond, simplifiedStmts);
            shared_ptr<Expr> thenExpr = simplify(condExpr->thenExpr, simplifiedStmts);
            shared_ptr<Expr> elseExpr = simplify(condExpr->elseExpr, simplifiedStmts);
            shared_ptr<CondExpr> simplifiedExpr = make_shared<CondExpr>(cond, thenExpr, elseExpr, expr->sourcePos);
            return simplifiedExpr;
        }
        case CaseExprType:
            //FIXME case expr
            return expr;
        case MatchesExprType: {
            shared_ptr<Expr> simplifiedExpr = simplify(expr->matchesExpr(), simplifiedStmts);
            return simplifiedExpr;
        }
        case EnumUnionStructExprType:
            logstream << "FIXME: simplify expr: " << endl;
            expr->prettyPrint(logstream, 0);
            logstream << endl;
            return expr;
        case InterfaceExprType: {
            shared_ptr<InterfaceExpr> interfaceExpr = expr->interfaceExpr();
            assert(!interfaceExpr->stmts.size());
            vector<shared_ptr<Stmt>> stmts;
            for (int i = 0; i < interfaceExpr->stmts.size(); i++) {
                simplify(interfaceExpr->stmts[i], stmts);
            }
            shared_ptr<InterfaceExpr> simplifiedExpr = make_shared<InterfaceExpr>(interfaceExpr->bsvtype, stmts, interfaceExpr->sourcePos);
            return simplifiedExpr;
        }
        case ValueofExprType:
            assert(expr->exprType != ValueofExprType);
            return expr;
    }
    return expr;
}

shared_ptr<Expr>
SimplifyAst::simplify(const shared_ptr<MatchesExpr> &matchesExpr, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    shared_ptr<Expr> matchesPattern = matchPattern(matchesExpr->pattern, simplifiedStmts);
    for (int i = 0; i < matchesExpr->patterncond.size(); i++) {
        matchesPattern = make_shared<OperatorExpr>("==", matchesPattern,
                                                   simplify(matchesExpr->patterncond[i], simplifiedStmts),
                                                   matchesExpr->sourcePos);
    }

    return matchesPattern;
}

shared_ptr<Expr>
SimplifyAst::matchPattern(const shared_ptr<Pattern> &pattern, vector<shared_ptr<struct Stmt>> &simplifiedStmts) {
    //FIXME: sourcePos
    return make_shared<VarExpr>("fixme_pattern_match", make_shared<BSVType>("PatternType"), SourcePos());
}
