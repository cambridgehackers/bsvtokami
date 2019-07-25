#include "GenerateAst.h"

using namespace std;

shared_ptr<Expr> GenerateAst::expr(BSVParser::ExpressionContext *ctx) {
    shared_ptr<Expr> result;
    BSVParser::OperatorexprContext *oc = dynamic_cast<BSVParser::OperatorexprContext *>(ctx);
    if (oc) {
        BSVParser::BinopexprContext *binopexpr = oc->binopexpr();
        result = expr(binopexpr);
    }
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::CaseexpritemContext *ctx) {
    shared_ptr<Expr> result;
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::CaseexprdefaultitemContext *ctx) {
    shared_ptr<Expr> result;
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::BinopexprContext *ctx) {
    if (ctx->unopexpr()) {
        return expr(ctx->unopexpr());
    }
    shared_ptr<Expr> lhs(expr(ctx->left));
    shared_ptr<Expr> rhs(expr(ctx->right));
    string op(ctx->op->getText());
    shared_ptr<Expr> result(new OperatorExpr(op, lhs, rhs));
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::UnopexprContext *ctx) {
    shared_ptr<Expr> result;
    shared_ptr<Expr> arg(expr(ctx->exprprimary()));
    if (ctx->op) {
        if (!arg)
            cerr << "unhandled expr: " << ctx->exprprimary()->getText() << endl;
        result.reset(new OperatorExpr(ctx->op->getText(), arg));
    } else {
        result = arg;
    }
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::ExprprimaryContext *ctx) {
    shared_ptr<Expr> result;
    if (BSVParser::FieldexprContext *fieldexpr = dynamic_cast<BSVParser::FieldexprContext *>(ctx)) {
        shared_ptr<Expr> object(expr(fieldexpr->exprprimary()));
        result.reset(new FieldExpr(object, fieldexpr->field->getText()));
    } else if (BSVParser::VarexprContext *varexpr = dynamic_cast<BSVParser::VarexprContext *>(ctx)) {
        result.reset(new VarExpr(varexpr->getText()));
    } else if (BSVParser::IntliteralContext *intliteral = dynamic_cast<BSVParser::IntliteralContext *>(ctx)) {
        result.reset(new IntConst(intliteral->getText()));
    } else if (BSVParser::ArraysubContext *arraysub = dynamic_cast<BSVParser::ArraysubContext *>(ctx)) {
        shared_ptr<Expr> array(expr(arraysub->array));
        shared_ptr<Expr> msb(expr(arraysub->msb));
        shared_ptr<Expr> lsb;
        if (arraysub->lsb)
            lsb = expr(arraysub->lsb);
        result.reset(new ArraySubExpr(array, msb, lsb));
    } else if (BSVParser::CallexprContext *callexpr = dynamic_cast<BSVParser::CallexprContext *>(ctx)) {
        shared_ptr<Expr> function(expr(callexpr->fcn));
        vector<BSVParser::ExpressionContext *> args = callexpr->expression();
        vector<shared_ptr<Expr>> exprs;
        for (size_t i = 0; i < args.size(); i++) {
            exprs.push_back(expr(args.at(i)));
        }
        result.reset(new CallExpr(function, exprs));
    } else if (BSVParser::TaggedunionexprContext *unionexpr = dynamic_cast<BSVParser::TaggedunionexprContext *>(ctx)) {
        string tag = unionexpr->upperCaseIdentifier(0)->getText();
        vector<string> keys;
        vector<shared_ptr<Expr>> vals;
        BSVParser::MemberbindsContext *memberbinds = unionexpr->memberbinds();
        if (memberbinds) {
            vector<BSVParser::MemberbindContext*> memberbindvec = memberbinds->memberbind();
            for (size_t i = 0; i < memberbindvec.size(); i++) {
                BSVParser::MemberbindContext *memberbind = memberbindvec.at(i);
                keys.push_back(memberbind->lowerCaseIdentifier()->getText());
                vals.push_back(expr(memberbind->expression()));
            }
        } else {
            //FIXME
            cerr << "unhandled tagged union: " << unionexpr->getText() << endl;
        }

        result.reset(new EnumUnionStructExpr(tag, keys, vals));
    } else {
        cerr << "Unhandled expr " << ctx->getText() << endl;
    }
    return result;
}

void GenerateAst::generateAst(BSVParser::PackagedefContext *ctx) {
    vector<BSVParser::PackagestmtContext *> stmts = ctx->packagestmt();
    fprintf(stderr, "generateAst %lu stmts\n", stmts.size());
    for (size_t i = 0; i < stmts.size(); i++) {
        generateAst(stmts.at(i));
    }
}

void GenerateAst::generateAst(BSVParser::PackagestmtContext *ctx) {
    vector<shared_ptr<Stmt>> package_stmts;
    if (ctx->moduledef() != NULL) {
        generateAst(ctx->moduledef());
    } else if (BSVParser::VarbindingContext *varbinding = ctx->varbinding()) {
        shared_ptr<Stmt> stmt = generateAst(varbinding);
        stmt->prettyPrint(0);
        package_stmts.push_back(stmt);
    } else if (BSVParser::ImportdeclContext *importdecl = ctx->importdecl()) {
        //FIXME: package specifier
        shared_ptr<Stmt> stmt(new ImportStmt(importdecl->upperCaseIdentifier(0)->getText()));
        stmt->prettyPrint(0);
        package_stmts.push_back(stmt);
    } else if (BSVParser::InterfacedeclContext *interfacedecl = ctx->interfacedecl()) {
        shared_ptr<Stmt> stmt = generateAst(interfacedecl);
        stmt->prettyPrint(0);
        package_stmts.push_back(stmt);
    } else if (BSVParser::TypedefsynonymContext *synonym = ctx->typedefsynonym()) {
        shared_ptr<BSVType> type(bsvtype(synonym->bsvtype()));
        shared_ptr<BSVType> typedeftype(bsvtype(synonym->typedeftype()));
        shared_ptr<Stmt> stmt(new TypedefSynonymStmt(typedeftype, type));
        stmt->prettyPrint(0);
        package_stmts.push_back(stmt);
    } else if (BSVParser::TypedefstructContext *def = ctx->typedefstruct()) {
        //FIXME: package name
        string name(def->typedeftype()->typeide()->getText());
        shared_ptr<BSVType> structType(bsvtype(def->typedeftype()));
        vector<BSVParser::StructmemberContext *> structmembers = def->structmember();
        vector<string> memberNames;
        vector<shared_ptr<BSVType>> memberTypes;
        for (size_t i = 0; i < structmembers.size(); i++) {
            BSVParser::StructmemberContext *member = structmembers[i];
            memberNames.push_back(member->lowerCaseIdentifier()->getText());
            memberTypes.push_back(bsvtype(member->bsvtype()));
        }
        shared_ptr<Stmt> stmt(new TypedefStructStmt(name, structType, memberNames, memberTypes));
        stmt->prettyPrint(0);
        package_stmts.push_back(stmt);
    } else {
        cerr << "unhandled packagestmt" << ctx->getText() << endl;
    }
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::InterfacedeclContext *ctx) {
    string interfaceName(ctx->typedeftype()->typeide()->name->getText());
    fprintf(stderr, "interfacedecl %s\n", interfaceName.c_str());
    shared_ptr<BSVType> interfaceType(bsvtype(ctx->typedeftype()));
    vector<shared_ptr<Stmt>> ast_members;
    vector<BSVParser::InterfacememberdeclContext *> members = ctx->interfacememberdecl();
    for (size_t i = 0; i < members.size(); i++) {
        BSVParser::InterfacememberdeclContext *member = members[i];
        if (BSVParser::MethodprotoContext *methodproto = member->methodproto()) {
            string methodName(methodproto->lowerCaseIdentifier()->getText());
            shared_ptr<BSVType> returnType(bsvtype(methodproto->bsvtype()));
            vector<string> params;
            vector<shared_ptr<BSVType>> paramTypes;
            shared_ptr<Stmt> methoddecl(new MethodDeclStmt(methodName, returnType, params, paramTypes));
            ast_members.push_back(methoddecl);

        }
    }

    shared_ptr<Stmt> interfacedecl(new InterfaceDeclStmt(interfaceName, interfaceType, ast_members));
    return interfacedecl;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ModuledefContext *ctx) {
    BSVParser::ModuleprotoContext *moduleproto = ctx->moduleproto();
    string moduleName(moduleproto->lowerCaseIdentifier()->getText());
    fprintf(stderr, "moduledef %s\n", moduleName.c_str());
    shared_ptr<BSVType> interfaceType(bsvtype(moduleproto->bsvtype()));
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    BSVParser::MethodprotoformalsContext *formals = ctx->moduleproto()->methodprotoformals();
    if (formals) {
        vector<BSVParser::MethodprotoformalContext *> formalvec = formals->methodprotoformal();
        for (size_t i = 0; i < formalvec.size(); i++) {
            BSVParser::MethodprotoformalContext *formal = formalvec.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            paramTypes.push_back(bsvtype(formal->bsvtype()));
        }
    }
    vector<BSVParser::ModulestmtContext *> stmts = ctx->modulestmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        BSVParser::ModulestmtContext *modstmt = stmts.at(i);
        if (modstmt->methoddef() != 0) {
            ast_stmts.push_back(generateAst(modstmt->methoddef()));
        } else if (modstmt->stmt() != 0) {
            BSVParser::StmtContext *stmt = modstmt->stmt();
            if (stmt->ruledef() != 0) {
                shared_ptr<Stmt> ruledef = generateAst(stmt->ruledef());
                ast_stmts.push_back(ruledef);
            }
        }
    }
    shared_ptr<Stmt> moduledef(new ModuleDefStmt(moduleName, interfaceType,
            params, paramTypes,
            ast_stmts));
    moduledef->prettyPrint();
    return moduledef;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::MethoddefContext *ctx) {
    string methodName(ctx->lowerCaseIdentifier(0)->getText());
    shared_ptr<BSVType> returnType(bsvtype(ctx->bsvtype()));
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    shared_ptr<Expr> guard;

    vector<BSVParser::MethodformalContext*> formals = ctx->methodformals()->methodformal();
    for (size_t i = 0; i < formals.size(); i++) {
        BSVParser::MethodformalContext *formal = formals.at(i);
        params.push_back(formal->lowerCaseIdentifier()->getText());
        paramTypes.push_back(bsvtype(formal->bsvtype()));
    }
    fprintf(stderr, "    methoddef %s\n", methodName.c_str());
    if (ctx->methodcond() != 0) {
        //fprintf(stderr, "      when %s\n", ctx->methodcond()->getText().c_str());
        guard = expr(ctx->methodcond()->expression());
    }
    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt)
            cerr << "unhandled method stmt: " << stmts.at(i)->getText() << endl;
        ast_stmts.push_back(stmt);
    }
    return shared_ptr<Stmt>(new MethodDefStmt(methodName, returnType,
            params, paramTypes, guard, ast_stmts));
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::RuledefContext *ctx) {
    string ruleName(ctx->lowerCaseIdentifier(0)->getText());
    fprintf(stderr, "    ruledef %s\n", ruleName.c_str());
    shared_ptr<Expr> guard;
    if (ctx->rulecond() != 0) {
        fprintf(stderr, "      when %s\n", ctx->rulecond()->getText().c_str());
        guard = expr(ctx->rulecond()->expression());
    }

    shared_ptr<RuleDefStmt> ruledef(new RuleDefStmt(ruleName, guard));
    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt)
            cerr << "unhandled rule stmt: " << stmts.at(i)->getText();
        ruledef->addStmt(stmt);
    }
    return ruledef;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::StmtContext *ctx) {
    shared_ptr<Stmt> stmt;
    //fprintf(stderr, "        stmt %s\n", ctx->getText().c_str());
    if (BSVParser::RegwriteContext *regwrite = ctx->regwrite()) {
        string regName(regwrite->lhs->getText());
        shared_ptr<Expr> rhs(expr(regwrite->rhs));
        stmt.reset(new RegWriteStmt(regName, rhs));
    } else if (BSVParser::VarbindingContext *varbinding = ctx->varbinding()) {
        stmt = generateAst(varbinding);
    } else if (BSVParser::ActionbindingContext *actionbinding = ctx->actionbinding()) {
        stmt = generateAst(actionbinding);
    } else if (BSVParser::IfstmtContext *ifstmt = ctx->ifstmt()) {
        shared_ptr<Expr> condition(expr(ifstmt->expression()));
        shared_ptr<Stmt> thenStmt(generateAst(ifstmt->stmt(0)));
        shared_ptr<Stmt> elseStmt;
        if (ifstmt->stmt(1))
            elseStmt = generateAst(ifstmt->stmt(1));
        return shared_ptr<Stmt>(new IfStmt(condition, thenStmt, elseStmt));
    } else if (BSVParser::BeginendblockContext *block = ctx->beginendblock()) {
        vector<BSVParser::StmtContext *> stmts = block->stmt();
        vector<shared_ptr<Stmt>> ast_stmts;
        for (size_t i = 0; i < stmts.size(); i++) {
            shared_ptr<Stmt> ast_stmt(generateAst(stmts.at(i)));
            if (!ast_stmt)
                cerr << "unhandled block stmt: " << stmts.at(i)->getText() << endl;
            ast_stmts.push_back(ast_stmt);
        }
        return shared_ptr<Stmt>(new BlockStmt(ast_stmts));
    } else if (BSVParser::ReturnstmtContext *ret_stmt = ctx->returnstmt()){
        shared_ptr<Expr> val(expr(ret_stmt->expression()));
        return shared_ptr<Stmt> (new RetStmt(val));
    } else if (BSVParser::ExpressionContext *exp_stmt = ctx->expression()) {
        shared_ptr<Expr> val(expr(exp_stmt));
        return shared_ptr<Stmt> (new ExprStmt(val));
    }
    return stmt;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::VarbindingContext *varbinding) {
    string varName = varbinding->lowerCaseIdentifier()->getText();
    shared_ptr<BSVType> varType;
    if (varbinding->t)
        varType = bsvtype(varbinding->t);
    else
        varType.reset(new BSVType());
    shared_ptr<Expr> rhs(expr(varbinding->rhs));
    if (!rhs)
        cerr << "var binding unhandled rhs: " << varbinding->expression()->getText() << endl;
    return shared_ptr<Stmt>(new VarBindingStmt(varType, varName, rhs));
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ActionbindingContext *actionbinding) {
    string varName = actionbinding->lowerCaseIdentifier()->getText();
    shared_ptr<BSVType> varType;
    if (actionbinding->t)
        varType = bsvtype(actionbinding->t);
    else
        varType.reset(new BSVType());
    shared_ptr<Expr> rhs(expr(actionbinding->rhs));
    return shared_ptr<Stmt>(new ActionBindingStmt(varType, varName, rhs));
}

std::shared_ptr<BSVType> GenerateAst::bsvtype(BSVParser::BsvtypeContext *ctx) {
    if (BSVParser::TypeideContext *typeide = ctx->typeide()) {
        //FIXME: package prefix
        string typeName = typeide->upperCaseIdentifier(0)->getText();
        vector<BSVParser::BsvtypeContext *> params = ctx->bsvtype();
        vector<shared_ptr<BSVType>> typeParams;
        for (size_t i = 0; i < params.size(); i++) {
            typeParams.push_back(bsvtype(params.at(i)));
        }
        return shared_ptr<BSVType>(new BSVType(typeName, typeParams));
    } else if (ctx->var) {
        string typeName = ctx->var->getText();
        return shared_ptr<BSVType>(new BSVType(typeName));
    } else if (ctx->typenat()) {
        shared_ptr<BSVType> numericType(new BSVType(ctx->typenat()->getText(), true, false));
        return numericType;
    } else if (ctx->bsvtype(0)) {
        return bsvtype(ctx->bsvtype(0));
    }
    cerr << "unhandled bsvtype: " << ctx->getText() << endl;
    return shared_ptr<BSVType>(new BSVType("<fixme>"));
}

std::shared_ptr<BSVType> GenerateAst::bsvtype(BSVParser::TypedeftypeContext *ctx) {
    string name = ctx->typeide()->upperCaseIdentifier(0)->getText();
    vector<shared_ptr<BSVType>> typeParams;
    if (ctx->typeformals()) {
        vector<BSVParser::TypeformalContext *> formals = ctx->typeformals()->typeformal();
        for (size_t i = 0; i < formals.size(); i++) {
            BSVParser::TypeformalContext *formal = formals[i];
            typeParams.push_back(shared_ptr<BSVType>(new BSVType(formal->typeide()->getText())));
        }
    }
    return shared_ptr<BSVType>(new BSVType(name, typeParams));
}
