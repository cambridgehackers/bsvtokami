//
// Created by Jamey Hicks on 1/27/20.
//

#include "AstVisitor.h"

void AstVisitor::visit(const shared_ptr<Stmt> &stmt) {
    switch (stmt->stmtType) {
        case ActionBindingStmtType:
            visitActionBindingStmt(stmt->actionBindingStmt());
            break;
        case BlockStmtType:
            visitBlockStmt(stmt->blockStmt());
            break;
        case CallStmtType:
            visitCallStmt(stmt->callStmt());
            break;
        case ExprStmtType:
            visitExprStmt(stmt->exprStmt());
            break;
        case FunctionDefStmtType:
            visitFunctionDefStmt(stmt->functionDefStmt());
            break;
        case InterfaceDeclStmtType:
            visitInterfaceDeclStmt(stmt->interfaceDeclStmt());
            break;
        case InterfaceDefStmtType:
            //visitInterfaceDefStmt(stmt->interfaceDefStmt());
            break;
        case IfStmtType:
            visitIfStmt(stmt->ifStmt());
            break;
        case ImportStmtType:
            visitImportStmt(stmt->importStmt());
            break;
        case MethodDeclStmtType:
            visitMethodDeclStmt(stmt->methodDeclStmt());
            break;
        case MethodDefStmtType:
            //visitMethodDefStmt(stmt->methodDefStmt());
            break;
        case ModuleDefStmtType:
            visitModuleDef(stmt->moduleDefStmt());
            break;
        case ModuleInstStmtType:
            visitModuleInstStmt(stmt->moduleInstStmt());
            break;
        case PackageDefStmtType:
            visitPackageDefStmt(stmt->packageDefStmt());
            break;
        case PatternMatchStmtType:
            visitPatternMatchStmt(stmt->patternMatchStmt());
            break;
        case RegisterStmtType:
            visitRegisterStmt(stmt->registerStmt());
            break;
        case RegReadStmtType:
            visitRegReadStmt(stmt->regReadStmt());
            break;
        case RegWriteStmtType:
            visitRegWriteStmt(stmt->regWriteStmt());
            break;
        case ReturnStmtType:
            visitReturnStmt(stmt->returnStmt());
            break;
        case TypedefEnumStmtType:
            visitTypedefEnumStmt(stmt->typedefEnumStmt());
            break;
        case TypedefStructStmtType:
            visitTypedefStructStmt(stmt->typedefStructStmt());
            break;
        case TypedefSynonymStmtType:
            visitTypedefSynonymStmt(stmt->typedefSynonymStmt());
            break;
        case VarBindingStmtType:
            visitVarBindingStmt(stmt->varBindingStmt());
            break;
        case VarAssignStmtType:
            visitVarAssignStmt(stmt->varAssignStmt());
            break;
        case RuleDefStmtType:
            visitRuleDefStmt(stmt->ruleDefStmt());
            break;
        case InvalidStmtType:
            assert(stmt->stmtType != InvalidStmtType);
            break;
    }
}

void AstVisitor::visitModuleDef(const shared_ptr<ModuleDefStmt> &moduleDef) {
    for (int i = 0; i < moduleDef->stmts.size(); i++)
        visit(moduleDef->stmts[i]);
}

void AstVisitor::visitActionBindingStmt(const shared_ptr<ActionBindingStmt> &stmt) {
    visit(stmt->rhs);
}

void AstVisitor::visitBlockStmt(const shared_ptr<BlockStmt> stmt) {
    for (int i = 0; i < stmt->stmts.size(); i++)
        visit(stmt->stmts[i]);
}

void AstVisitor::visitCallStmt(const shared_ptr<CallStmt> stmt) {
    visit(stmt->rhs);
}

void AstVisitor::visitExprStmt(const shared_ptr<ExprStmt> stmt) {
    visit(stmt->expr);
}

void AstVisitor::visitFunctionDefStmt(const shared_ptr<FunctionDefStmt> stmt) {
    for (int i = 0; i < stmt->stmts.size(); i++)
        visit(stmt->stmts[i]);
}

void AstVisitor::visitInterfaceDeclStmt(const shared_ptr<InterfaceDeclStmt> sharedPtr) {

}

void AstVisitor::visitIfStmt(const shared_ptr<IfStmt> stmt) {
    visit(stmt->condition);
    visit(stmt->thenStmt);
    visit(stmt->elseStmt);
}

void AstVisitor::visitImportStmt(const shared_ptr<ImportStmt> stmt) {

}

void AstVisitor::visitMethodDeclStmt(const shared_ptr<MethodDeclStmt> stmt) {
}

void AstVisitor::visitModuleInstStmt(const shared_ptr<ModuleInstStmt> stmt) {

}

void AstVisitor::visitPackageDefStmt(const shared_ptr<PackageDefStmt> stmt) {
    for (int i = 0; i < stmt->stmts.size(); i++)
        visit(stmt->stmts[i]);
}

void AstVisitor::visitPatternMatchStmt(const shared_ptr<PatternMatchStmt> sharedPtr) {

}

void AstVisitor::visitRegisterStmt(const shared_ptr<RegisterStmt> sharedPtr) {

}

void AstVisitor::visitRegReadStmt(const shared_ptr<RegReadStmt> stmt) {
}

void AstVisitor::visitRegWriteStmt(const shared_ptr<RegWriteStmt> stmt) {
    visit(stmt->rhs);
}

void AstVisitor::visitReturnStmt(const shared_ptr<ReturnStmt> stmt) {
    visit(stmt->value);
}

void AstVisitor::visitTypedefEnumStmt(const shared_ptr<TypedefEnumStmt> stmt) {

}

void AstVisitor::visitTypedefStructStmt(const shared_ptr<TypedefStructStmt> stmt) {

}

void AstVisitor::visitTypedefSynonymStmt(const shared_ptr<TypedefSynonymStmt> stmt) {

}

void AstVisitor::visitVarBindingStmt(const shared_ptr<VarBindingStmt> stmt) {
    visit(stmt->rhs);
}

void AstVisitor::visitVarAssignStmt(const shared_ptr<VarAssignStmt> stmt) {
    visit(stmt->rhs);
}

void AstVisitor::visitRuleDefStmt(const shared_ptr<RuleDefStmt> stmt) {
    visit(stmt->guard);
    for (int i = 0; i < stmt->stmts.size(); i++)
        visit(stmt->stmts[i]);
}

void AstVisitor::visit(const shared_ptr<Expr> &expr) {
    switch (expr->exprType) {
        case InvalidExprType:
            assert(expr->exprType != InvalidExprType);
            break;
        case ArraySubExprType:
            visitArraySubExpr(expr->arraySubExpr());
            break;
        case BitConcatExprType:
            visitBitConcatExpr(expr->bitConcatExpr());
            break;
        case BitSelExprType:
            visitBitSelExpr(expr->bitSelExpr());
            break;
        case VarExprType:
            visitVarExpr(expr->varExpr());
            break;
        case IntConstType:
            visitIntConst(expr->intConst());
            break;
        case InterfaceExprType:
            visitInterfaceExpr(expr->interfaceExpr());
            break;
        case SubinterfaceExprType:
            visitSubinterfaceExpr(expr->subinterfaceExpr());
            break;
        case StringConstType:
            visitStringConst(expr->stringConst());
            break;
        case OperatorExprType:
            visitOperatorExpr(expr->operatorExpr());
            break;
        case CallExprType:
            visitCallExpr(expr->callExpr());
            break;
        case FieldExprType:
            visitFieldExpr(expr->fieldExpr());
            break;
        case CondExprType:
            visitCondExpr(expr->condExpr());
            break;
        case CaseExprType:
            visitCaseExpr(expr->caseExpr());
            break;
        case EnumUnionStructExprType:
            visitEnumUnionStructExpr(expr->enumUnionStructExpr());
            break;
        case MatchesExprType:
            visitMatchesExpr(expr->matchesExpr());
            break;
        case MethodExprType:
            visitMethodExpr(expr->methodExpr());
            break;
        case ValueofExprType:
            visitValueofExpr(expr->valueofExpr());
            break;
    }
}

void AstVisitor::visitArraySubExpr(const shared_ptr<ArraySubExpr> expr) {
    visit(expr->array);
    visit(expr->index);
}

void AstVisitor::visitBitConcatExpr(const shared_ptr<BitConcatExpr> expr) {

}

void AstVisitor::visitBitSelExpr(const shared_ptr<BitSelExpr> expr) {

}

void AstVisitor::visitVarExpr(const shared_ptr<VarExpr> expr) {

}

void AstVisitor::visitIntConst(const shared_ptr<IntConst> expr) {

}

void AstVisitor::visitInterfaceExpr(const shared_ptr<InterfaceExpr> expr) {

}

void AstVisitor::visitSubinterfaceExpr(const shared_ptr<SubinterfaceExpr> expr) {

}

void AstVisitor::visitStringConst(const shared_ptr<StringConst> expr) {

}

void AstVisitor::visitOperatorExpr(const shared_ptr<OperatorExpr> expr) {

}

void AstVisitor::visitCallExpr(const shared_ptr<CallExpr> expr) {

}

void AstVisitor::visitFieldExpr(const shared_ptr<FieldExpr> expr) {

}

void AstVisitor::visitCondExpr(const shared_ptr<CondExpr> expr) {

}

void AstVisitor::visitCaseExpr(const shared_ptr<CaseExpr> expr) {

}

void AstVisitor::visitEnumUnionStructExpr(const shared_ptr<EnumUnionStructExpr> expr) {

}

void AstVisitor::visitMatchesExpr(const shared_ptr<MatchesExpr> expr) {

}

void AstVisitor::visitMethodExpr(const shared_ptr<MethodExpr> expr) {

}

void AstVisitor::visitValueofExpr(const shared_ptr<ValueofExpr> expr) {

}

void AstVisitor::visit(const shared_ptr<BSVType> &bsvtype) {
}
