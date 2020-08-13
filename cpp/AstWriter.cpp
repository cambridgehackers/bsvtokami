//
// Created by Jamey Hicks on 8/11/20.
//

#include <iostream>
#include <fstream>

#include "AstWriter.h"

AstWriter::AstWriter() {}

AstWriter::~AstWriter() noexcept {}

void AstWriter::visit(const shared_ptr<Stmt> &stmt, bsvproto::Stmt *stmt_proto) {
    cerr << "AstWriter::visit stmt " << stmt->stmtType << endl;
    switch (stmt->stmtType) {
        case InvalidStmtType:
            break;
        case ActionBindingStmtType:
            visitActionBindingStmt(stmt->actionBindingStmt(), stmt_proto);
            break;
        case BlockStmtType:
            visitBlockStmt(stmt->blockStmt(), stmt_proto);
            break;
        case CallStmtType:
            visitCallStmt(stmt->callStmt(), stmt_proto);
            break;
        case ExprStmtType:
            visitExprStmt(stmt->exprStmt(), stmt_proto);
            break;
        case FunctionDefStmtType:
            visitFunctionDefStmt(stmt->functionDefStmt(), stmt_proto);
            break;
        case InterfaceDeclStmtType:
            visitInterfaceDeclStmt(stmt->interfaceDeclStmt(), stmt_proto);
            break;
        case InterfaceDefStmtType:
            visitInterfaceDefStmt(stmt->interfaceDefStmt(), stmt_proto);
            break;
        case IfStmtType:
            visitIfStmt(stmt->ifStmt(), stmt_proto);
            break;
        case ImportStmtType:
            visitImportStmt(stmt->importStmt(), stmt_proto);
            break;
        case MethodDeclStmtType:
            visitMethodDeclStmt(stmt->methodDeclStmt(), stmt_proto);
            break;
        case MethodDefStmtType:
            visitMethodDefStmt(stmt->methodDefStmt(), stmt_proto);
            break;
        case ModuleDefStmtType:
            visitModuleDefStmt(stmt->moduleDefStmt(), stmt_proto);
            break;
        case ModuleInstStmtType:
            visitModuleInstStmt(stmt->moduleInstStmt(), stmt_proto);
            break;
        case PackageDefStmtType:
            // stmt_proto is null
            visitPackageDefStmt(stmt->packageDefStmt());
            break;
        case PatternMatchStmtType:
            visitPatternMatchStmt(stmt->patternMatchStmt(), stmt_proto);
            break;
        case RegisterStmtType:
            visitRegisterStmt(stmt->registerStmt(), stmt_proto);
            break;
        case RegReadStmtType:
            visitRegReadStmt(stmt->regReadStmt(), stmt_proto);
            break;
        case RegWriteStmtType:
            visitRegWriteStmt(stmt->regWriteStmt(), stmt_proto);
            break;
        case ReturnStmtType:
            visitReturnStmt(stmt->returnStmt(), stmt_proto);
            break;
        case TypedefEnumStmtType:
            visitTypedefEnumStmt(stmt->typedefEnumStmt(), stmt_proto);
            break;
        case TypedefStructStmtType:
            visitTypedefStructStmt(stmt->typedefStructStmt(), stmt_proto);
            break;
        case TypedefSynonymStmtType:
            visitTypedefSynonymStmt(stmt->typedefSynonymStmt(), stmt_proto);
            break;
        case VarBindingStmtType:
            visitVarBindingStmt(stmt->varBindingStmt(), stmt_proto);
            break;
        case VarAssignStmtType:
            visitVarAssignStmt(stmt->varAssignStmt(), stmt_proto);
            break;
        case RuleDefStmtType:
            visitRuleDefStmt(stmt->ruleDefStmt(), stmt_proto);
            break;
    }
}

void AstWriter::visitModuleDefStmt(const shared_ptr<ModuleDefStmt> &moduledef, bsvproto::Stmt *stmt_proto) {
    cerr << "visitModuleDefStmt" << endl;
    bsvproto::ModuleDefStmt moduledef_proto;
    moduledef_proto.set_name(moduledef->name);
    moduledef_proto.set_package(moduledef->package);
    visit(moduledef->interfaceType, moduledef_proto.mutable_returntype());
    for (int i = 0; i < moduledef->params.size(); i++) {
        moduledef_proto.add_paramname(moduledef->params[i]);
        visit(moduledef->paramTypes[i], moduledef_proto.add_paramtype());
    }
    for (int i = 0; i < moduledef->stmts.size(); i++) {
        bsvproto::Stmt *substmt_proto = moduledef_proto.add_stmt();
        visit(moduledef->stmts[i], substmt_proto);
    }

    *stmt_proto->mutable_moduledefstmt() = moduledef_proto;
}

void AstWriter::visitPackageDefStmt(const shared_ptr<PackageDefStmt> packageDef) {
    cerr << "visitPackageDefStmt" << endl;
    packagedef_proto.set_name(packageDef->name);
    bsvproto::SourcePos *sourcePos = newSourcePos(packageDef->sourcePos);
    packagedef_proto.set_allocated_sourcepos(sourcePos);
    for (int i = 0; i < packageDef->stmts.size(); i++) {
        bsvproto::Stmt *substmt_proto = packagedef_proto.add_stmt();
        visit(packageDef->stmts[i], substmt_proto);
    }
}

bsvproto::SourcePos *AstWriter::newSourcePos(const SourcePos &sourcePos) {
    bsvproto::SourcePos *sourcePos_proto = new bsvproto::SourcePos();
    sourcePos_proto->set_filename(sourcePos.sourceName);
    sourcePos_proto->set_linenumber(sourcePos.line);
    return sourcePos_proto;
}

bool AstWriter::writeAst(std::string filename) {
    ofstream output(filename, ios::out | ios::trunc | ios::binary);
    packagedef_proto.SerializeToOstream(&output);
    output.close();
    return true;
}

void AstWriter::visitActionBindingStmt(shared_ptr<ActionBindingStmt> actionBindingStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitActionBindingStmt " << actionBindingStmt->name << endl;
    bsvproto::ActionBindingStmt actionBindingStmt_proto;
    actionBindingStmt_proto.set_name(actionBindingStmt->name);
    visit(actionBindingStmt->bsvtype, actionBindingStmt_proto.mutable_bsvtype());
    visit(actionBindingStmt->rhs, actionBindingStmt_proto.mutable_rhs());
    *stmt_proto->mutable_actionbindingstmt() = actionBindingStmt_proto;
}

void AstWriter::visitBlockStmt(shared_ptr<BlockStmt> blockStmt, bsvproto::Stmt *stmt_proto) {
    bsvproto::BlockStmt blockStmt_proto;
    for (int i = 0; i < blockStmt->stmts.size(); i++) {
        bsvproto::Stmt *substmt_proto = blockStmt_proto.add_stmt();
        visit(blockStmt->stmts[i], substmt_proto);
    }
    *stmt_proto->mutable_blockstmt() = blockStmt_proto;
}

void AstWriter::visitCallStmt(shared_ptr<CallStmt> callStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitCallStmt" << endl;
    bsvproto::CallStmt callStmt_proto;
    bsvproto::Expr *expr_proto = callStmt_proto.mutable_rhs();
    visit(callStmt->rhs, expr_proto);
    *stmt_proto->mutable_callstmt() = callStmt_proto;

}

void AstWriter::visitExprStmt(shared_ptr<ExprStmt> exprStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitExprStmt" << endl;
    bsvproto::ExprStmt exprStmt_proto;
    bsvproto::Expr *expr_proto = exprStmt_proto.mutable_expr();
    visit(exprStmt->expr, expr_proto);
    *stmt_proto->mutable_exprstmt() = exprStmt_proto;
}

void AstWriter::visitFunctionDefStmt(shared_ptr<FunctionDefStmt> functionDefStmt, bsvproto::Stmt *stmt_proto) {

}

void AstWriter::visitInterfaceDeclStmt(shared_ptr<InterfaceDeclStmt> interfaceDeclStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitInterfaceDeclStmt" << endl;
    bsvproto::InterfaceDeclStmt interfaceDeclStmt_proto;
    interfaceDeclStmt_proto.set_name(interfaceDeclStmt->name);
    interfaceDeclStmt_proto.set_package(interfaceDeclStmt->package);
    //FIXME: more fields
    *stmt_proto->mutable_interfacedeclstmt() = interfaceDeclStmt_proto;
}

void AstWriter::visitInterfaceDefStmt(shared_ptr<InterfaceDefStmt> interfaceDefStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitInterfaceDefStmt " << interfaceDefStmt->name << endl;
}

void AstWriter::visitIfStmt(shared_ptr<IfStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitIfStmt" << endl;
}

void AstWriter::visitImportStmt(shared_ptr<ImportStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitImportStmt" << endl;
}

void AstWriter::visitMethodDeclStmt(shared_ptr<MethodDeclStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitMethodDefStmt" << endl;
}

void AstWriter::visitMethodDefStmt(shared_ptr<MethodDefStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitMethodDefStmt" << endl;
}

void AstWriter::visitModuleInstStmt(shared_ptr<ModuleInstStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitModuleInstStmt" << endl;
}

void AstWriter::visitPatternMatchStmt(shared_ptr<PatternMatchStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitPatternMatchStmt" << endl;
}

void AstWriter::visitRegisterStmt(shared_ptr<RegisterStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRegisterStmt" << endl;
}

void AstWriter::visitRegReadStmt(shared_ptr<RegReadStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRegReadStmt" << endl;
}

void AstWriter::visitRegWriteStmt(shared_ptr<RegWriteStmt> regWriteStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRegWriteStmt" << endl;
}

void AstWriter::visitReturnStmt(shared_ptr<ReturnStmt> returnStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitReturnStmt" << endl;
}

void AstWriter::visitTypedefEnumStmt(shared_ptr<TypedefEnumStmt> typedefEnumStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitTypedefEnumStmt" << endl;
}

void AstWriter::visitTypedefStructStmt(shared_ptr<TypedefStructStmt> typedefStructStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitTypedefStructStmt" << endl;
}

void AstWriter::visitTypedefSynonymStmt(shared_ptr<TypedefSynonymStmt> typedefSynonymStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitTypedefSynonymStmt" << endl;
}

void AstWriter::visitVarBindingStmt(shared_ptr<VarBindingStmt> varBindingStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitVarAssignStmt" << endl;
}

void AstWriter::visitVarAssignStmt(shared_ptr<VarAssignStmt> varAssignStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitVarAssignStmt" << endl;
}

void AstWriter::visitRuleDefStmt(shared_ptr<RuleDefStmt> ruleDefStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRuleDefStmt" << endl;
    bsvproto::RuleDefStmt ruleDefStmt_proto;
    ruleDefStmt_proto.set_name(ruleDefStmt->name);
    if (ruleDefStmt->guard) {
        visit(ruleDefStmt->guard, ruleDefStmt_proto.mutable_guard());
    }
    for (int i = 0; i < ruleDefStmt->stmts.size(); i++) {
        bsvproto::Stmt *substmt_proto = ruleDefStmt_proto.add_stmt();
        visit(ruleDefStmt->stmts[i], substmt_proto);
    }
    *stmt_proto->mutable_ruledefstmt() = ruleDefStmt_proto;
}

void AstWriter::visit(const shared_ptr<Expr> &expr, bsvproto::Expr *expr_proto) {
    cerr << "visit expr " << expr->exprType << endl;
    switch (expr->exprType) {
        case InvalidExprType:
            //visitInvalidExpr(expr->invalidExpr(), expr_proto);
            break;
        case ArraySubExprType:
            visitArraySubExpr(expr->arraySubExpr(), expr_proto);
            break;
        case BitConcatExprType:
            visitBitConcatExpr(expr->bitConcatExpr(), expr_proto);
            break;
        case BitSelExprType:
            visitBitSelExpr(expr->bitSelExpr(), expr_proto);
            break;
        case VarExprType:
            visitVarExpr(expr->varExpr(), expr_proto);
            break;
        case IntConstType:
            visitIntConst(expr->intConst(), expr_proto);
            break;
        case InterfaceExprType:
            visitInterfaceExpr(expr->interfaceExpr(), expr_proto);
            break;
        case SubinterfaceExprType:
            visitSubinterfaceExpr(expr->subinterfaceExpr(), expr_proto);
            break;
        case StringConstType:
            visitStringConst(expr->stringConst(), expr_proto);
            break;
        case OperatorExprType:
            visitOperatorExpr(expr->operatorExpr(), expr_proto);
            break;
        case CallExprType:
            visitCallExpr(expr->callExpr(), expr_proto);
            break;
        case FieldExprType:
            visitFieldExpr(expr->fieldExpr(), expr_proto);
            break;
        case CondExprType:
            visitCondExpr(expr->condExpr(), expr_proto);
            break;
        case CaseExprType:
            visitCaseExpr(expr->caseExpr(), expr_proto);
            break;
        case EnumUnionStructExprType:
            visitEnumUnionStructExpr(expr->enumUnionStructExpr(), expr_proto);
            break;
        case MatchesExprType:
            visitMatchesExpr(expr->matchesExpr(), expr_proto);
            break;
        case MethodExprType:
            visitMethodExpr(expr->methodExpr(), expr_proto);
            break;
        case ValueofExprType:
            visitValueofExpr(expr->valueofExpr(), expr_proto);
            break;
    }

}

void AstWriter::visitArraySubExpr(shared_ptr<ArraySubExpr> arraySubExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitBitConcatExpr(shared_ptr<BitConcatExpr> bitConcatExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitBitSelExpr(shared_ptr<BitSelExpr> bitSelExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitVarExpr(shared_ptr<VarExpr> varExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitVarExpr " << varExpr->sourceName << endl;
    bsvproto::VarExpr varExpr_proto;
    varExpr_proto.set_sourcename(varExpr->sourceName);
    varExpr_proto.set_uniquename(varExpr->name);
    visit(varExpr->bsvtype, varExpr_proto.mutable_bsvtype());
    *expr_proto->mutable_varexpr() = varExpr_proto;
}

void AstWriter::visitIntConst(shared_ptr<IntConst> intConst, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitInterfaceExpr(shared_ptr<InterfaceExpr> interfaceExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitSubinterfaceExpr(shared_ptr<SubinterfaceExpr> subinterfaceExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitStringConst(shared_ptr<StringConst> stringConst, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitOperatorExpr(shared_ptr<OperatorExpr> operatorExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitCallExpr(shared_ptr<CallExpr> callExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitFieldExpr(shared_ptr<FieldExpr> fieldExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitCondExpr(shared_ptr<CondExpr> condExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitCaseExpr(shared_ptr<CaseExpr> caseExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitEnumUnionStructExpr(shared_ptr<EnumUnionStructExpr> enumUnionStructExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitMatchesExpr(shared_ptr<MatchesExpr> matchesExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitMethodExpr(shared_ptr<MethodExpr> methodExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visitValueofExpr(shared_ptr<ValueofExpr> valueofExpr, bsvproto::Expr *expr_proto) {

}

void AstWriter::visit(const shared_ptr<BSVType> &bsvtype, bsvproto::BSVType *bsvtype_proto) {
    cerr << "visit bsvtype " << bsvtype->name << endl;
    bsvtype_proto->set_name(bsvtype->name);
    bsvtype_proto->set_isvar(bsvtype->isVar);
    bsvtype_proto->set_kind(bsvtype->kind == BSVType_Symbolic ? bsvproto::Symbolic : bsvproto::Numeric);
    for (int i = 0; i < bsvtype->params.size(); i++) {
        visit(bsvtype->params[i], bsvtype_proto->add_param());
    }
}