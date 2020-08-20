//
// Created by Jamey Hicks on 8/11/20.
//

#include <iostream>
#include <fstream>

#include "AstWriter.h"

AstWriter::AstWriter() {}

AstWriter::~AstWriter() noexcept {}

void AstWriter::visit(const shared_ptr <Stmt> &stmt, bsvproto::Stmt *stmt_proto) {
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

void AstWriter::visitModuleDefStmt(const shared_ptr <ModuleDefStmt> &moduledef, bsvproto::Stmt *stmt_proto) {
    cerr << "visitModuleDefStmt" << endl;
    bsvproto::ModuleDefStmt moduledef_proto;
    visit(moduledef->sourcePos, moduledef_proto.mutable_sourcepos());
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

void AstWriter::visitPackageDefStmt(const shared_ptr <PackageDefStmt> packageDef) {
    cerr << "visitPackageDefStmt" << endl;
    packagedef_proto.set_name(packageDef->name);
    packagedef_proto.set_filename(packageDef->sourcePos.sourceName);
    visit(packageDef->sourcePos, packagedef_proto.mutable_sourcepos());
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
    output << packagedef_proto.SerializeAsString();
    output.close();
    return true;
}

void AstWriter::visitActionBindingStmt(shared_ptr <ActionBindingStmt> actionBindingStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitActionBindingStmt " << actionBindingStmt->name << endl;
    bsvproto::ActionBindingStmt actionBindingStmt_proto;
    actionBindingStmt_proto.set_name(actionBindingStmt->name);
    visit(actionBindingStmt->sourcePos, actionBindingStmt_proto.mutable_sourcepos());
    visit(actionBindingStmt->bsvtype, actionBindingStmt_proto.mutable_bsvtype());
    visit(actionBindingStmt->rhs, actionBindingStmt_proto.mutable_rhs());

    *stmt_proto->mutable_actionbindingstmt() = actionBindingStmt_proto;
}

void AstWriter::visitBlockStmt(shared_ptr <BlockStmt> blockStmt, bsvproto::Stmt *stmt_proto) {
    bsvproto::BlockStmt blockStmt_proto;
    for (int i = 0; i < blockStmt->stmts.size(); i++) {
        bsvproto::Stmt *substmt_proto = blockStmt_proto.add_stmt();
        visit(blockStmt->stmts[i], substmt_proto);
    }

    *stmt_proto->mutable_blockstmt() = blockStmt_proto;
}

void AstWriter::visitCallStmt(shared_ptr <CallStmt> callStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitCallStmt" << endl;
    bsvproto::CallStmt callStmt_proto;
    callStmt_proto.set_name(callStmt->name);
    visit(callStmt->interfaceType, callStmt_proto.mutable_vartype());
    visit(callStmt->rhs, callStmt_proto.mutable_rhs());

    *stmt_proto->mutable_callstmt() = callStmt_proto;
}

void AstWriter::visitExprStmt(shared_ptr <ExprStmt> exprStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitExprStmt" << endl;
    bsvproto::ExprStmt exprStmt_proto;
    visit(exprStmt->sourcePos, exprStmt_proto.mutable_sourcepos());
    bsvproto::Expr *expr_proto = exprStmt_proto.mutable_expr();
    visit(exprStmt->expr, expr_proto);

    *stmt_proto->mutable_exprstmt() = exprStmt_proto;
}

void AstWriter::visitFunctionDefStmt(shared_ptr <FunctionDefStmt> functionDefStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitFunctionDefStmt" << endl;
    bsvproto::FunctionDefStmt functionDefStmt_proto;
    visit(functionDefStmt->sourcePos, functionDefStmt_proto.mutable_sourcepos());
    functionDefStmt_proto.set_package(functionDefStmt->package);
    functionDefStmt_proto.set_name(functionDefStmt->name);
    visit(functionDefStmt->returnType, functionDefStmt_proto.mutable_returntype());
    for (int i = 0; i < functionDefStmt->params.size(); i++) {
        functionDefStmt_proto.add_paramname(functionDefStmt->params[i]);
        visit(functionDefStmt->paramTypes[i], functionDefStmt_proto.add_paramtype());
    }
    for (int i = 0; i < functionDefStmt->stmts.size(); i++) {
        visit(functionDefStmt->stmts[i], functionDefStmt_proto.add_stmt());
    }
    if (functionDefStmt->guard) {
        visit(functionDefStmt->guard, functionDefStmt_proto.mutable_guard());
    }

    *stmt_proto->mutable_functiondefstmt() = functionDefStmt_proto;

}

void AstWriter::visitInterfaceDeclStmt(shared_ptr <InterfaceDeclStmt> interfaceDeclStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitInterfaceDeclStmt" << endl;
    bsvproto::InterfaceDeclStmt interfaceDeclStmt_proto;
    visit(interfaceDeclStmt->sourcePos, interfaceDeclStmt_proto.mutable_sourcepos());
    interfaceDeclStmt_proto.set_name(interfaceDeclStmt->name);
    interfaceDeclStmt_proto.set_package(interfaceDeclStmt->package);
    //FIXME: more fields

    *stmt_proto->mutable_interfacedeclstmt() = interfaceDeclStmt_proto;
}

void AstWriter::visitInterfaceDefStmt(shared_ptr <InterfaceDefStmt> interfaceDefStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitInterfaceDefStmt " << interfaceDefStmt->name << endl;
    bsvproto::InterfaceDefStmt interfaceDefStmt_proto;
    visit(interfaceDefStmt->sourcePos, interfaceDefStmt_proto.mutable_sourcepos());
    //FIXME: more fields

    *stmt_proto->mutable_interfacedefstmt() = interfaceDefStmt_proto;
}

void AstWriter::visitIfStmt(shared_ptr <IfStmt> ifStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitIfStmt" << endl;
    bsvproto::IfStmt ifStmt_proto;
    visit(ifStmt->sourcePos, ifStmt_proto.mutable_sourcepos());
    visit(ifStmt->condition, ifStmt_proto.mutable_condition());
    visit(ifStmt->thenStmt, ifStmt_proto.mutable_thenstmt());
    visit(ifStmt->elseStmt, ifStmt_proto.mutable_elsestmt());

    *stmt_proto->mutable_ifstmt() = ifStmt_proto;
}

void AstWriter::visitImportStmt(shared_ptr <ImportStmt> importStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitImportStmt" << endl;
    bsvproto::ImportStmt importStmt_proto;
    visit(importStmt->sourcePos, importStmt_proto.mutable_sourcepos());
    importStmt_proto.set_name(importStmt->name);

    *stmt_proto->mutable_importstmt() = importStmt_proto;
}

void AstWriter::visitMethodDeclStmt(shared_ptr <MethodDeclStmt> methodDeclStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitMethodDefStmt" << endl;
    bsvproto::MethodDeclStmt methodDeclStmt_proto;
    visit(methodDeclStmt->sourcePos, methodDeclStmt_proto.mutable_sourcepos());
    methodDeclStmt_proto.set_name(methodDeclStmt->name);
    visit(methodDeclStmt->returnType, methodDeclStmt_proto.mutable_returntype());
    for (int i = 0; i < methodDeclStmt->params.size(); i++) {
        methodDeclStmt_proto.add_paramname(methodDeclStmt->params[i]);
        visit(methodDeclStmt->paramTypes[i], methodDeclStmt_proto.add_paramtype());
    }

    *stmt_proto->mutable_methoddeclstmt() = methodDeclStmt_proto;
}

void AstWriter::visitMethodDefStmt(shared_ptr <MethodDefStmt> methodDefStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitMethodDefStmt" << endl;
    bsvproto::MethodDefStmt methodDefStmt_proto;
    visit(methodDefStmt->sourcePos, methodDefStmt_proto.mutable_sourcepos());
    methodDefStmt_proto.set_name(methodDefStmt->name);
    visit(methodDefStmt->returnType, methodDefStmt_proto.mutable_returntype());
    for (int i = 0; i < methodDefStmt->params.size(); i++) {
        methodDefStmt_proto.add_paramname(methodDefStmt->params[i]);
        visit(methodDefStmt->paramTypes[i], methodDefStmt_proto.add_paramtype());
    }
    visit(methodDefStmt->guard, methodDefStmt_proto.mutable_guard());

    *stmt_proto->mutable_methoddefstmt() = methodDefStmt_proto;
}

void AstWriter::visitModuleInstStmt(shared_ptr <ModuleInstStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitModuleInstStmt" << endl;
    //FIXME
}

void AstWriter::visitPatternMatchStmt(shared_ptr <PatternMatchStmt> patternMatchStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitPatternMatchStmt" << endl;
    bsvproto::PatternMatchStmt patternMatchStmt_proto;
    visit(patternMatchStmt->sourcePos, patternMatchStmt_proto.mutable_sourcepos());
    visit(patternMatchStmt->pattern, patternMatchStmt_proto.mutable_pattern());

    *stmt_proto->mutable_patternmatchstmt() = patternMatchStmt_proto;
}

void AstWriter::visitRegisterStmt(shared_ptr <RegisterStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRegisterStmt" << endl;
    //FIXME
}

void AstWriter::visitRegReadStmt(shared_ptr <RegReadStmt> sharedPtr, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRegReadStmt" << endl;
    //FIXME
}

void AstWriter::visitRegWriteStmt(shared_ptr <RegWriteStmt> regWriteStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRegWriteStmt" << endl;
    //FIXME
}

void AstWriter::visitReturnStmt(shared_ptr <ReturnStmt> returnStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitReturnStmt" << endl;
    bsvproto::ReturnStmt returnStmt_proto;
    visit(returnStmt->sourcePos, returnStmt_proto.mutable_sourcepos());
    visit(returnStmt->value, returnStmt_proto.mutable_returnexpr());
    if (returnStmt->value)
        visit(returnStmt->value->bsvtype, returnStmt_proto.mutable_returntype());

    *stmt_proto->mutable_returnstmt() = returnStmt_proto;
}

void AstWriter::visitTypedefEnumStmt(shared_ptr <TypedefEnumStmt> typedefEnumStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitTypedefEnumStmt" << endl;
    //FIXME
}

void AstWriter::visitTypedefStructStmt(shared_ptr <TypedefStructStmt> typedefStructStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitTypedefStructStmt" << endl;
    //FIXME
}

void
AstWriter::visitTypedefSynonymStmt(shared_ptr <TypedefSynonymStmt> typedefSynonymStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitTypedefSynonymStmt" << endl;
    //FIXME
}

void AstWriter::visitVarBindingStmt(shared_ptr <VarBindingStmt> varBindingStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitVarBindingStmt" << endl;
    bsvproto::VarBindingStmt varBindingStmt_proto;
    visit(varBindingStmt->sourcePos, varBindingStmt_proto.mutable_sourcepos());
    varBindingStmt_proto.set_package(varBindingStmt->package);
    visit(varBindingStmt->bsvtype, varBindingStmt_proto.mutable_bsvtype());
    varBindingStmt_proto.set_name(varBindingStmt->name);
    varBindingStmt_proto.set_op(bsvproto::VALUE);
    visit(varBindingStmt->rhs, varBindingStmt_proto.mutable_rhs());

    *stmt_proto->mutable_varbindingstmt() = varBindingStmt_proto;
}

void AstWriter::visitVarAssignStmt(shared_ptr <VarAssignStmt> varAssignStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitVarAssignStmt" << endl;
    bsvproto::VarAssignStmt varAssignStmt_proto;
    visit(varAssignStmt->sourcePos, varAssignStmt_proto.mutable_sourcepos());
    visit(varAssignStmt->lhs, varAssignStmt_proto.mutable_lvalue());
    varAssignStmt_proto.set_op(varAssignStmt->op == "<-" ? bsvproto::ACTION : bsvproto::VALUE);
    visit(varAssignStmt->rhs, varAssignStmt_proto.mutable_rhs());

    *stmt_proto->mutable_varassignstmt() = varAssignStmt_proto;
}

void AstWriter::visitRuleDefStmt(shared_ptr <RuleDefStmt> ruleDefStmt, bsvproto::Stmt *stmt_proto) {
    cerr << "visitRuleDefStmt" << endl;
    bsvproto::RuleDefStmt ruleDefStmt_proto;
    visit(ruleDefStmt->sourcePos, ruleDefStmt_proto.mutable_sourcepos());
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

void AstWriter::visit(const shared_ptr <Expr> &expr, bsvproto::Expr *expr_proto) {
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

void AstWriter::visitArraySubExpr(shared_ptr <ArraySubExpr> arraySubExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitArraySubExpr" << endl;
    bsvproto::ArraySubExpr arraySubExpr_proto;
    visit(arraySubExpr->bsvtype, arraySubExpr_proto.mutable_bsvtype());
    visit(arraySubExpr->array, arraySubExpr_proto.mutable_array());
    visit(arraySubExpr->index, arraySubExpr_proto.mutable_index());

    *expr_proto->mutable_arraysubexpr() = arraySubExpr_proto;
}

void AstWriter::visitBitConcatExpr(shared_ptr <BitConcatExpr> bitConcatExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitBitConcatExpr" << endl;
    bsvproto::BitConcatExpr bitConcatExpr_proto;
    visit(bitConcatExpr->bsvtype, bitConcatExpr_proto.mutable_bsvtype());
    for (int i = 0; i < bitConcatExpr->values.size(); i++) {
        visit(bitConcatExpr->values[i], bitConcatExpr_proto.add_value());
    }

    *expr_proto->mutable_bitconcatexpr() = bitConcatExpr_proto;
}

void AstWriter::visitBitSelExpr(shared_ptr <BitSelExpr> bitSelExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitBitSelExpr" << endl;

    bsvproto::BitSelExpr bitSelExpr_proto;
    visit(bitSelExpr->bsvtype, bitSelExpr_proto.mutable_bsvtype());
    visit(bitSelExpr->value, bitSelExpr_proto.mutable_value());
    visit(bitSelExpr->msb, bitSelExpr_proto.mutable_msb());
    if (bitSelExpr->lsb)
        visit(bitSelExpr->lsb, bitSelExpr_proto.mutable_lsb());

    *expr_proto->mutable_bitselexpr() = bitSelExpr_proto;
}

void AstWriter::visitVarExpr(shared_ptr <VarExpr> varExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitVarExpr " << varExpr->sourceName << endl;
    bsvproto::VarExpr varExpr_proto;
    varExpr_proto.set_sourcename(varExpr->sourceName);
    varExpr_proto.set_uniquename(varExpr->name);
    visit(varExpr->bsvtype, varExpr_proto.mutable_bsvtype());

    *expr_proto->mutable_varexpr() = varExpr_proto;
}

void AstWriter::visitIntConst(shared_ptr <IntConst> intConst, bsvproto::Expr *expr_proto) {
    bsvproto::IntConst intConst_proto;
    intConst_proto.set_value(intConst->value);
    intConst_proto.set_base(intConst->base);
    intConst_proto.set_width(intConst->width);

    *expr_proto->mutable_intconst() = intConst_proto;
}

void AstWriter::visitInterfaceExpr(shared_ptr <InterfaceExpr> interfaceExpr, bsvproto::Expr *expr_proto) {
    cerr << "FIXME visitInterfaceExpr" << endl;
}

void AstWriter::visitSubinterfaceExpr(shared_ptr <SubinterfaceExpr> subinterfaceExpr, bsvproto::Expr *expr_proto) {
    cerr << "FIXME visitSubinterfaceExpr" << endl;

}

void AstWriter::visitStringConst(shared_ptr <StringConst> stringConst, bsvproto::Expr *expr_proto) {
    bsvproto::StringConst stringConst_proto;
    stringConst_proto.set_value(stringConst->repr);

    *expr_proto->mutable_stringconst() = stringConst_proto;
}

void AstWriter::visitOperatorExpr(shared_ptr <OperatorExpr> operatorExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitOperatorExpr " << operatorExpr->op << endl;
    bsvproto::OperatorExpr operatorExpr_proto;
    if (operatorExpr->bsvtype)
        visit(operatorExpr->bsvtype, operatorExpr_proto.mutable_bsvtype());
    operatorExpr_proto.set_op(operatorExpr->op);
    visit(operatorExpr->lhs, operatorExpr_proto.mutable_lhs());
    visit(operatorExpr->rhs, operatorExpr_proto.mutable_rhs());

    *expr_proto->mutable_operatorexpr() = operatorExpr_proto;
}

void AstWriter::visitCallExpr(shared_ptr <CallExpr> callExpr, bsvproto::Expr *expr_proto) {
    cerr << "visitCallExpr " << endl;
    bsvproto::CallExpr callExpr_proto;
    if (callExpr->bsvtype)
        visit(callExpr->bsvtype, callExpr_proto.mutable_bsvtype());
    visit(callExpr->function, callExpr_proto.mutable_function());
    for (int i = 0; i < callExpr->args.size(); i++) {
        visit(callExpr->args[i], callExpr_proto.add_arg());
    }

    *expr_proto->mutable_callexpr() = callExpr_proto;
}

void AstWriter::visitFieldExpr(shared_ptr <FieldExpr> fieldExpr, bsvproto::Expr *expr_proto) {
    bsvproto::FieldExpr fieldExpr_proto;
    if (fieldExpr->bsvtype)
        visit(fieldExpr->bsvtype, fieldExpr_proto.mutable_bsvtype());
    visit(fieldExpr->object, fieldExpr_proto.mutable_object());
    fieldExpr_proto.set_fieldname(fieldExpr->fieldName);

    *expr_proto->mutable_fieldexpr() = fieldExpr_proto;
}

void AstWriter::visitCondExpr(shared_ptr <CondExpr> condExpr, bsvproto::Expr *expr_proto) {
    bsvproto::CondExpr condExpr_proto;
    if (condExpr->bsvtype)
        visit(condExpr->bsvtype, condExpr_proto.mutable_bsvtype());
    visit(condExpr->cond, condExpr_proto.mutable_cond());
    visit(condExpr->thenExpr, condExpr_proto.mutable_thenexpr());
    visit(condExpr->elseExpr, condExpr_proto.mutable_elseexpr());

    *expr_proto->mutable_condexpr() = condExpr_proto;
}

void AstWriter::visitCaseExpr(shared_ptr <CaseExpr> caseExpr, bsvproto::Expr *expr_proto) {
    cerr << "FIXME: visitCaseExpr" << endl;
}

void
AstWriter::visitEnumUnionStructExpr(shared_ptr <EnumUnionStructExpr> enumUnionStructExpr, bsvproto::Expr *expr_proto) {
    cerr << "FIXME: visitEnumUnionStructExpr" << endl;
}

void AstWriter::visitMatchesExpr(shared_ptr <MatchesExpr> matchesExpr, bsvproto::Expr *expr_proto) {
    bsvproto::MatchesExpr matchesExpr_proto;
    if (matchesExpr->bsvtype)
        visit(matchesExpr->bsvtype, matchesExpr_proto.mutable_bsvtype());
    visit(matchesExpr->expr, matchesExpr_proto.mutable_expr());
    visit(matchesExpr->pattern, matchesExpr_proto.mutable_pattern());
    for (int i = 0; i < matchesExpr->patterncond.size(); i++) {
        visit(matchesExpr->patterncond[i], matchesExpr_proto.add_patterncond());
    }
    *expr_proto->mutable_matchesexpr() = matchesExpr_proto;
}

void AstWriter::visitMethodExpr(shared_ptr <MethodExpr> methodExpr, bsvproto::Expr *expr_proto) {
    cerr << "FIXME: visitMethodExpr" << endl;
}

void AstWriter::visitValueofExpr(shared_ptr <ValueofExpr> valueofExpr, bsvproto::Expr *expr_proto) {
    bsvproto::ValueofExpr valueofExpr_proto;
    if (valueofExpr->bsvtype)
        visit(valueofExpr->bsvtype, valueofExpr_proto.mutable_bsvtype());
    visit(valueofExpr->argtype, valueofExpr_proto.mutable_argtype());

    *expr_proto->mutable_valueofexpr() = valueofExpr_proto;
}

void AstWriter::visit(const shared_ptr <BSVType> &bsvtype, bsvproto::BSVType *bsvtype_proto) {
    cerr << "visit bsvtype " << bsvtype->name << endl;
    bsvtype_proto->set_name(bsvtype->name);
    bsvtype_proto->set_isvar(bsvtype->isVar);
    bsvtype_proto->set_kind(bsvtype->kind == BSVType_Symbolic ? bsvproto::Symbolic : bsvproto::Numeric);
    for (int i = 0; i < bsvtype->params.size(); i++) {
        visit(bsvtype->params[i], bsvtype_proto->add_param());
    }
}

void AstWriter::visit(const SourcePos &sourcePos, bsvproto::SourcePos *sourcePos_proto) {
    sourcePos_proto->set_filename(sourcePos.sourceName);
    sourcePos_proto->set_linenumber(sourcePos.line);
}

void AstWriter::visit(const shared_ptr <Pattern> &pattern, bsvproto::Pattern *pattern_proto) {
    cerr << "visitPattern " << endl;
    switch (pattern->patternType) {
        case InvalidPatternType:
            cerr << "InvalidPatternType" << endl;
            break;
        case IntPatternType:
            visitIntPattern(pattern->intPattern(), pattern_proto);
            break;
        case TaggedPatternType:
            visitTaggedPattern(pattern->taggedPattern(), pattern_proto);
            break;
        case TuplePatternType:
            visitTuplePattern(pattern->tuplePattern(), pattern_proto);
            break;
        case VarPatternType:
            visitVarPattern(pattern->varPattern(), pattern_proto);
            break;
        case WildcardPatternType:
            visitWildcardPattern(pattern->wildcardPattern(), pattern_proto);
            break;
    }
}


void AstWriter::visitIntPattern(const shared_ptr <IntPattern> &intPattern, bsvproto::Pattern *pattern_proto) {
    bsvproto::IntPattern intPattern_proto;
    intPattern_proto.set_value(intPattern->value);

    *pattern_proto->mutable_intpattern() = intPattern_proto;
}

void AstWriter::visitTaggedPattern(const shared_ptr <TaggedPattern> &taggedPattern,
                                   bsvproto::Pattern *pattern_proto) {
    bsvproto::TaggedPattern taggedPattern_proto;
    taggedPattern_proto.set_name(taggedPattern->value);
    if (taggedPattern->pattern)
        visit(taggedPattern->pattern, taggedPattern_proto.mutable_pattern());

    *pattern_proto->mutable_taggedpattern() = taggedPattern_proto;
}

void
AstWriter::visitTuplePattern(const shared_ptr <TuplePattern> &tuplePattern, bsvproto::Pattern *pattern_proto) {
    bsvproto::TuplePattern tuplePattern_proto;
    for (int i = 0; i < tuplePattern->subpatterns.size(); i++) {
        visit(tuplePattern->subpatterns[i], tuplePattern_proto.add_subpattern());
    }
    *pattern_proto->mutable_tuplepattern() = tuplePattern_proto;
}

void AstWriter::visitVarPattern(const shared_ptr <VarPattern> &varPattern, bsvproto::Pattern *pattern_proto) {
    bsvproto::VarPattern varPattern_proto;
    varPattern_proto.set_name(varPattern->value);
    *pattern_proto->mutable_varpattern() = varPattern_proto;
}

void AstWriter::visitWildcardPattern(const shared_ptr <WildcardPattern> &wildcardPattern,
                                     bsvproto::Pattern *pattern_proto) {
    bsvproto::WildcardPattern wildcardPattern_proto;
    *pattern_proto->mutable_wildcardpattern() = wildcardPattern_proto;
}

void AstWriter::visit(const shared_ptr <LValue> &lvalue, bsvproto::LValue *lvalue_proto) {
    cerr << "visit LValue " << lvalue->lvalueType << endl;
    switch (lvalue->lvalueType) {
        case InvalidLValueType:
            break;
        case ArraySubLValueType:
            visitArraySubLValue(lvalue->arraySubLValue(), lvalue_proto);
            break;
        case FieldLValueType:
            visitFieldLValue(lvalue->fieldLValue(), lvalue_proto);
            break;
        case VarLValueType:
            visitVarLValue(lvalue->varLValue(), lvalue_proto);
            break;
        case RangeSelLValueType:
            visitRangeSelLValue(lvalue->rangeSelLValue(), lvalue_proto);
            break;
    }
}

void AstWriter::visitArraySubLValue(const shared_ptr<ArraySubLValue> &arraySubLValue, bsvproto::LValue *lvalue_proto) {
    bsvproto::ArraySubLValue arraySubLValue_proto;
    visit(arraySubLValue->array, arraySubLValue_proto.mutable_array());
    visit(arraySubLValue->index, arraySubLValue_proto.mutable_index());

    *lvalue_proto->mutable_array() = arraySubLValue_proto;
}

void AstWriter::visitFieldLValue(const shared_ptr<FieldLValue> &fieldLValue, bsvproto::LValue *lvalue_proto) {
    bsvproto::FieldLValue fieldLValue_proto;
    visit(fieldLValue->obj, fieldLValue_proto.mutable_obj());
    fieldLValue_proto.set_field(fieldLValue->field);

    *lvalue_proto->mutable_field() = fieldLValue_proto;
}

void AstWriter::visitVarLValue(const shared_ptr<VarLValue> &varLValue, bsvproto::LValue *lvalue_proto) {
    bsvproto::VarLValue varLValue_proto;
    varLValue_proto.set_name(varLValue->name);
    if (varLValue->bsvtype)
        visit(varLValue->bsvtype, varLValue_proto.mutable_bsvtype());

    *lvalue_proto->mutable_var() = varLValue_proto;
}

void AstWriter::visitRangeSelLValue(const shared_ptr<RangeSelLValue> &rangeSelLValue, bsvproto::LValue *lvalue_proto) {
    bsvproto::RangeSelLValue rangeSelLValue_proto;
    visit(rangeSelLValue->bitarray, rangeSelLValue_proto.mutable_array());
    visit(rangeSelLValue->lsb, rangeSelLValue_proto.mutable_lsb());
    visit(rangeSelLValue->msb, rangeSelLValue_proto.mutable_msb());

    *lvalue_proto->mutable_range() = rangeSelLValue_proto;
}
