#include "GenerateAst.h"

using namespace std;

std::shared_ptr<LValue> GenerateAst::lvalue(BSVParser::LvalueContext *lhs) {
    if (lhs->exprprimary() != nullptr) {
        shared_ptr<Expr> lhsLValue(expr(lhs->exprprimary()));
        if (lhs->index != nullptr) {
            return ArraySubLValue::create(lhsLValue, expr(lhs->index));
        } else if (lhs->msb != nullptr) {
            return RangeSelLValue::create(lhsLValue, expr(lhs->msb), expr(lhs->lsb));
        } else {
            return FieldLValue::create(lhsLValue, lhs->lowerCaseIdentifier()->getText());
        }
    } else {
        return VarLValue::create(lhs->lowerCaseIdentifier()->getText());
    }
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::ExpressionContext *ctx) {
    shared_ptr<Expr> result;
    if (BSVParser::OperatorexprContext *oc = dynamic_cast<BSVParser::OperatorexprContext *>(ctx)) {
        BSVParser::BinopexprContext *binopexpr = oc->binopexpr();
        return expr(binopexpr);
    } else if (BSVParser::CondexprContext *condexpr = dynamic_cast<BSVParser::CondexprContext *>(ctx)) {
        return expr(condexpr);
    } else if (BSVParser::MatchesexprContext *matchesExpr = dynamic_cast<BSVParser::MatchesexprContext *>(ctx)) {
        cerr << "Unhandled matches expr " << ctx->getText() << endl;
        return expr(matchesExpr);
    } else if (BSVParser::CaseexprContext *caseexpr = dynamic_cast<BSVParser::CaseexprContext *>(ctx)) {
        cerr << "Unhandled case expr " << ctx->getText() << endl;
        return result;
    }
    cerr << "How did we get here: expr " << ctx->getRuleIndex() << " " << ctx->getText() << endl;
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

std::shared_ptr<Expr> GenerateAst::expr(BSVParser::CondexprContext *ctx) {
    shared_ptr<Expr> condexpr(expr(ctx->pred));
    shared_ptr<Expr> thenexpr(expr(ctx->expression(0)));
    shared_ptr<Expr> elseexpr(expr(ctx->expression(1)));
    if (!condexpr || !thenexpr || !elseexpr) {
        cerr << "Funny cond expr: " << ctx->getText() << endl;
        cerr << (bool)condexpr << (bool)thenexpr << (bool)elseexpr << endl;
    }
    shared_ptr<Expr> result(new CondExpr(condexpr, thenexpr, elseexpr));
    return result;
}

std::shared_ptr<Expr> GenerateAst::expr(BSVParser::MatchesexprContext *ctx) {
    shared_ptr<Expr> lhs(expr(ctx->expression()));
    shared_ptr<Pattern> pattern = generateAst(ctx->pattern());
    vector<BSVParser::PatterncondContext *> patterncond = ctx->patterncond();
    if (patterncond.size()) {
        vector<shared_ptr<Expr>> exprs;
        for (int i = 0; i < patterncond.size(); i++)
            exprs.push_back(expr(patterncond[i]->expression()));
        return MatchesExpr::create(lhs, pattern, exprs);
    } else {
        return MatchesExpr::create(lhs, pattern);
    }
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
            cerr << "unhandled unop expr: " << ctx->exprprimary()->getText() << endl;
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
        return FieldExpr::create(object, fieldexpr->field->getText());
    } else if (BSVParser::VarexprContext *varexpr = dynamic_cast<BSVParser::VarexprContext *>(ctx)) {
        //FIXME: get type from type checker
        shared_ptr<BSVType> varType = typeChecker->lookup(varexpr);
        result.reset(new VarExpr(varexpr->getText(), varType));
    } else if (BSVParser::IntliteralContext *intliteral = dynamic_cast<BSVParser::IntliteralContext *>(ctx)) {
        result.reset(new IntConst(intliteral->getText()));
    } else if (BSVParser::StringliteralContext *stringliteral = dynamic_cast<BSVParser::StringliteralContext *>(ctx)) {
        result.reset(new StringConst(stringliteral->getText()));
    } else if (BSVParser::ArraysubContext *arraysub = dynamic_cast<BSVParser::ArraysubContext *>(ctx)) {
        shared_ptr<Expr> array(expr(arraysub->array));
        shared_ptr<Expr> msb(expr(arraysub->msb));
        if (arraysub->lsb) {
            shared_ptr<Expr> lsb(expr(arraysub->lsb));
            return make_shared<BitSelExpr>(array, msb, lsb);
        } else {
            return make_shared<ArraySubExpr>(array, msb);
        }
    } else if (BSVParser::CallexprContext *callexpr = dynamic_cast<BSVParser::CallexprContext *>(ctx)) {
        shared_ptr<Expr> function(expr(callexpr->fcn));
        vector<BSVParser::ExpressionContext *> args = callexpr->expression();
        vector<shared_ptr<Expr>> exprs;
        for (size_t i = 0; i < args.size(); i++) {
            exprs.push_back(expr(args.at(i)));
        }
        result.reset(new CallExpr(function, exprs));
    } else if (BSVParser::SyscallexprContext *syscallexpr = dynamic_cast<BSVParser::SyscallexprContext *>(ctx)) {
        //FIXME: placeholder type for $display etc.
        shared_ptr<VarExpr> function = make_shared<VarExpr>(syscallexpr->fcn->getText(), make_shared<BSVType>());
        vector<BSVParser::ExpressionContext *> args = syscallexpr->expression();
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
            vector<BSVParser::MemberbindContext *> memberbindvec = memberbinds->memberbind();
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
    } else if (BSVParser::ParenexprContext *parenexpr = dynamic_cast<BSVParser::ParenexprContext *>(ctx)) {
        return expr(parenexpr->expression());
    } else if (BSVParser::UndefinedexprContext *undef = dynamic_cast<BSVParser::UndefinedexprContext *>(ctx)) {
        //FIXME:: get type from type checker
        return shared_ptr<Expr>(new VarExpr("Undefined", make_shared<BSVType>()));
    } else {
        cerr << "Unhandled expr primary " << ctx->getText() << endl;
    }
    return result;
}

shared_ptr<PackageDefStmt> GenerateAst::generateAst(BSVParser::PackagedefContext *ctx) {
    vector<BSVParser::PackagestmtContext *> stmts = ctx->packagestmt();
    vector<shared_ptr<Stmt>> package_stmts;
    fprintf(stderr, "generateAst %lu stmts\n", stmts.size());
    string packageName("<unnamed>");
    for (size_t i = 0; i < stmts.size(); i++) {
        if (ctx->packagedecl()) {
            packageName = ctx->packagedecl()->packageide()->getText();
        }
        shared_ptr<Stmt> stmt = generateAst(stmts[i]);
        if (stmt)
            package_stmts.push_back(stmt);
    }
    return shared_ptr<PackageDefStmt>(new PackageDefStmt(packageName, package_stmts));
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::PackagestmtContext *ctx) {
    if (ctx->moduledef() != NULL) {
        return generateAst(ctx->moduledef());
    } else if (BSVParser::VarbindingContext *varbinding = ctx->varbinding()) {
        shared_ptr<Stmt> stmt = generateAst(varbinding);
        stmt->prettyPrint(cout, 0);
        return stmt;
    } else if (BSVParser::ImportdeclContext *importdecl = ctx->importdecl()) {
        //FIXME: package specifier
        shared_ptr<Stmt> stmt(new ImportStmt(importdecl->upperCaseIdentifier(0)->getText()));
        stmt->prettyPrint(cout, 0);
        return stmt;
    } else if (BSVParser::InterfacedeclContext *interfacedecl = ctx->interfacedecl()) {
        shared_ptr<Stmt> stmt = generateAst(interfacedecl);
        stmt->prettyPrint(cout, 0);
        return stmt;
    } else if (BSVParser::TypedefsynonymContext *synonym = ctx->typedefsynonym()) {
        shared_ptr<BSVType> type(TypeChecker::bsvtype(synonym->bsvtype()));
        shared_ptr<BSVType> typedeftype(TypeChecker::bsvtype(synonym->typedeftype()));
        shared_ptr<Stmt> stmt(new TypedefSynonymStmt(typedeftype, type));
        stmt->prettyPrint(cout, 0);
        return stmt;
    } else if (BSVParser::TypedefstructContext *def = ctx->typedefstruct()) {
        //FIXME: package name
        string name(def->typedeftype()->typeide()->getText());
        shared_ptr<BSVType> structType(TypeChecker::bsvtype(def->typedeftype()));
        vector<BSVParser::StructmemberContext *> structmembers = def->structmember();
        vector<string> memberNames;
        vector<shared_ptr<BSVType>> memberTypes;
        for (size_t i = 0; i < structmembers.size(); i++) {
            BSVParser::StructmemberContext *member = structmembers[i];
            memberNames.push_back(member->lowerCaseIdentifier()->getText());
            memberTypes.push_back(TypeChecker::bsvtype(member->bsvtype()));
        }
        shared_ptr<Stmt> stmt(new TypedefStructStmt(name, structType, memberNames, memberTypes));
        stmt->prettyPrint(cout, 0);
        return stmt;
    } else if (BSVParser::FunctiondefContext *fcn = ctx->functiondef()) {
        return generateAst(fcn);
    } else {
        cerr << "unhandled packagestmt" << ctx->getText() << endl;
    }
    return shared_ptr<Stmt>();
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::InterfacedeclContext *ctx) {
    string interfaceName(ctx->typedeftype()->typeide()->name->getText());
    fprintf(stderr, "interfacedecl %s\n", interfaceName.c_str());
    shared_ptr<BSVType> interfaceType(TypeChecker::bsvtype(ctx->typedeftype()));
    vector<shared_ptr<Stmt>> ast_members;
    vector<BSVParser::InterfacememberdeclContext *> members = ctx->interfacememberdecl();
    for (size_t i = 0; i < members.size(); i++) {
        BSVParser::InterfacememberdeclContext *member = members[i];
        if (BSVParser::MethodprotoContext *methodproto = member->methodproto()) {
            string methodName(methodproto->lowerCaseIdentifier()->getText());
            shared_ptr<BSVType> returnType(TypeChecker::bsvtype(methodproto->bsvtype()));
            vector<string> params;
            vector<shared_ptr<BSVType>> paramTypes;
            shared_ptr<Stmt> methoddecl(new MethodDeclStmt(methodName, returnType, params, paramTypes));
            ast_members.push_back(methoddecl);

        }
    }

    shared_ptr<Stmt> interfacedecl(new InterfaceDeclStmt(interfaceName, interfaceType, ast_members));
    return interfacedecl;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::SubinterfacedefContext *ctx) {
    string interfaceName(ctx->lowerCaseIdentifier(0)->getText());
    fprintf(stderr, "subinterfacedef %s\n", interfaceName.c_str());
    shared_ptr<BSVType> interfaceType(new BSVType(ctx->bsvtype() ? ctx->bsvtype()->typeide()->name->getText() : "<Interface TBD>"));
    vector<shared_ptr<Stmt>> ast_members;
    vector<BSVParser::InterfacestmtContext *> members = ctx->interfacestmt();
    for (size_t i = 0; i < members.size(); i++) {
        BSVParser::InterfacestmtContext *member = members[i];
        if (BSVParser::MethoddefContext *methoddef = member->methoddef()) {
            string methodName(methoddef->lowerCaseIdentifier(0)->getText());
            shared_ptr<BSVType> returnType(new BSVType());
            if (methoddef->bsvtype())
                returnType = TypeChecker::bsvtype(methoddef->bsvtype());
            vector<string> params;
            vector<shared_ptr<BSVType>> paramTypes;
            shared_ptr<Stmt> methoddecl(new MethodDeclStmt(methodName, returnType, params, paramTypes));
            ast_members.push_back(methoddecl);
        } else {
            cerr << "unhandled subinterface " << member->getText() << endl;
        }
    }

    shared_ptr<Stmt> interfacedef(new InterfaceDefStmt(interfaceName, interfaceType, ast_members));
    return interfacedef;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ModuledefContext *ctx) {
    BSVParser::ModuleprotoContext *moduleproto = ctx->moduleproto();
    string moduleName(moduleproto->lowerCaseIdentifier()->getText());
    fprintf(stderr, "moduledef %s\n", moduleName.c_str());
    shared_ptr<BSVType> interfaceType(TypeChecker::bsvtype(moduleproto->bsvtype()));
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    BSVParser::MethodprotoformalsContext *formals = ctx->moduleproto()->methodprotoformals();
    if (formals) {
        vector<BSVParser::MethodprotoformalContext *> formalvec = formals->methodprotoformal();
        for (size_t i = 0; i < formalvec.size(); i++) {
            BSVParser::MethodprotoformalContext *formal = formalvec.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            paramTypes.push_back(TypeChecker::bsvtype(formal->bsvtype()));
        }
    }
    vector<BSVParser::ModulestmtContext *> stmts = ctx->modulestmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        BSVParser::ModulestmtContext *modstmt = stmts.at(i);
        if (modstmt->methoddef() != 0) {
            ast_stmts.push_back(generateAst(modstmt->methoddef()));
        } else if (modstmt->moduleinst() != 0) {
            ast_stmts.push_back(generateAst(modstmt->moduleinst()));
        } else if (modstmt->stmt() != 0) {
            BSVParser::StmtContext *stmt = modstmt->stmt();
            shared_ptr<Stmt> astStmt(generateAst(stmt));
            if (!astStmt)
                cerr << "Empty ast stmt for " << stmt->getText() << endl;
            ast_stmts.push_back(astStmt);
        } else if (BSVParser::SubinterfacedefContext *subinterfacedef = modstmt->subinterfacedef()) {
            ast_stmts.push_back(generateAst(subinterfacedef));
        } else {
            cerr << "Unhandled module stmt: " << modstmt->getText() << endl;
        }
    }
    shared_ptr<Stmt> moduledef(new ModuleDefStmt(moduleName, interfaceType,
                                                 params, paramTypes,
                                                 ast_stmts));
    moduledef->prettyPrint(cout, 0);
    return moduledef;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::FunctiondefContext *ctx) {
    BSVParser::FunctionprotoContext *proto = ctx->functionproto();
    string functionName(proto->name->getText());
    shared_ptr<BSVType> returnType;
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    shared_ptr<Expr> guard;

    if (proto->bsvtype())
        returnType = TypeChecker::bsvtype(proto->bsvtype());
    else
        returnType.reset(new BSVType("Void"));

    if (proto->methodprotoformals()) {
        vector<BSVParser::MethodprotoformalContext *> formals = proto->methodprotoformals()->methodprotoformal();
        for (size_t i = 0; i < formals.size(); i++) {
            BSVParser::MethodprotoformalContext *formal = formals.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            if (formal->bsvtype() != nullptr) {
                paramTypes.push_back(TypeChecker::bsvtype(formal->bsvtype()));
            } else {
                fprintf(stderr, "functiondef formal with no type: %s at %s\n",
                        formal->getText().c_str(), sourceLocation(formal).c_str());
                paramTypes.push_back(shared_ptr<BSVType>(new BSVType()));

            }
        }
    }
    fprintf(stderr, "    methoddef %s\n", functionName.c_str());
    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt)
            cerr << "unhandled method stmt: " << stmts.at(i)->getText() << endl;
        ast_stmts.push_back(stmt);
    }
    return shared_ptr<Stmt>(new FunctionDefStmt(functionName, returnType,
                                                params, paramTypes, guard, ast_stmts));
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::MethoddefContext *ctx) {
    string methodName(ctx->lowerCaseIdentifier(0)->getText());
    shared_ptr<BSVType> returnType(TypeChecker::bsvtype(ctx->bsvtype()));
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    shared_ptr<Expr> guard;

    if (ctx->methodformals()) {
        vector<BSVParser::MethodformalContext *> formals = ctx->methodformals()->methodformal();
        for (size_t i = 0; i < formals.size(); i++) {
            BSVParser::MethodformalContext *formal = formals.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            if (formal->bsvtype() != nullptr) {
                paramTypes.push_back(TypeChecker::bsvtype(formal->bsvtype()));
            } else {
                fprintf(stderr, "methoddef formal with no type: %s at %s\n",
                        formal->getText().c_str(), sourceLocation(formal).c_str());
                paramTypes.push_back(shared_ptr<BSVType>(new BSVType()));
            }
        }
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

    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt)
            cerr << "unhandled rule stmt: " << stmts.at(i)->getText();
        ast_stmts.push_back(stmt);
    }
    shared_ptr<RuleDefStmt> ruledef(new RuleDefStmt(ruleName, guard, ast_stmts));
    return ruledef;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::StmtContext *ctx) {
    fprintf(stderr, "        stmt %s\n", ctx->getText().c_str());
    if (BSVParser::RegwriteContext *regwrite = ctx->regwrite()) {
        string regName(regwrite->lhs->getText());
        shared_ptr<Expr> rhs(expr(regwrite->rhs));
        return shared_ptr<Stmt>(new RegWriteStmt(regName, rhs));
    } else if (BSVParser::VarbindingContext *varbinding = ctx->varbinding()) {
        return generateAst(varbinding);
    } else if (BSVParser::ActionbindingContext *actionbinding = ctx->actionbinding()) {
        return generateAst(actionbinding);
    } else if (BSVParser::VarassignContext *varassign = ctx->varassign()) {
        shared_ptr<Stmt> stmt = generateAst(varassign);
        stmt->prettyPrint(cout, 0);
        return stmt;
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
    } else if (BSVParser::ActionblockContext *block = ctx->actionblock()) {
        vector<BSVParser::StmtContext *> stmts = block->stmt();
        vector<shared_ptr<Stmt>> ast_stmts;
        for (size_t i = 0; i < stmts.size(); i++) {
            shared_ptr<Stmt> ast_stmt(generateAst(stmts.at(i)));
            if (!ast_stmt)
                cerr << "unhandled block stmt: " << stmts.at(i)->getText() << endl;
            ast_stmts.push_back(ast_stmt);
        }
        return shared_ptr<Stmt>(new BlockStmt(ast_stmts));
    } else if (BSVParser::PatternbindingContext *patternBinding = ctx->patternbinding()) {
        shared_ptr<Expr> val(expr(patternBinding->expression()));
        shared_ptr<Pattern> pat = generateAst(patternBinding->pattern());
        return make_shared<PatternMatchStmt>(pat, patternBinding->op->getText(), val);
    } else if (BSVParser::ReturnstmtContext *ret_stmt = ctx->returnstmt()) {
        shared_ptr<Expr> val(expr(ret_stmt->expression()));
        return shared_ptr<Stmt>(new ReturnStmt(val));
    } else if (BSVParser::ExpressionContext *exp_stmt = ctx->expression()) {
        shared_ptr<Expr> val(expr(exp_stmt));
        return shared_ptr<Stmt>(new ExprStmt(val));
    } else if (BSVParser::RuledefContext *ruledef = ctx->ruledef()) {
        return generateAst(ruledef);
    } else if (BSVParser::FunctiondefContext *fcn = ctx->functiondef()) {
        cerr << "function stmt " << ctx->getText() << endl;
        return generateAst(fcn);
    } else {
        cerr << "Unhandled stmt: " << ctx->getText() << endl;
        return shared_ptr<Stmt>();
    }
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::VarbindingContext *varbinding) {
    shared_ptr<BSVType> varType;
    if (varbinding->t)
        varType = TypeChecker::bsvtype(varbinding->t);
    else
        varType.reset(new BSVType());
    std::vector<BSVParser::VarinitContext *> varinits = varbinding->varinit();
    for (size_t i = 0; i < varinits.size(); i++) {
        BSVParser::VarinitContext *varinit = varinits[i];
        string varName = varinit->lowerCaseIdentifier()->getText();
        shared_ptr<Expr> rhs(expr(varinit->rhs));
        if (!rhs)
            cerr << "var binding unhandled rhs: " << varinit->expression()->getText() << endl;
        return shared_ptr<Stmt>(new VarBindingStmt(varType, varName, rhs));
    }
    //FIXME: how to make multiple bindings?
    assert(0);
    return shared_ptr<Stmt>();
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ActionbindingContext *actionbinding) {
    string varName = actionbinding->lowerCaseIdentifier()->getText();
    shared_ptr<BSVType> varType;
    if (actionbinding->t)
        varType = TypeChecker::bsvtype(actionbinding->t);
    else
        varType.reset(new BSVType());
    shared_ptr<Expr> rhs(expr(actionbinding->rhs));

    cout << "action binding rhs ";
    expr(actionbinding->rhs)->prettyPrint(cout, 0); cout << endl;

    shared_ptr<Stmt> actionBindingStmt(new ActionBindingStmt(varType, varName, rhs));
    return actionBindingStmt;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::VarassignContext *varassign) {
    shared_ptr<LValue> lhs(lvalue(varassign->lvalue(0)));
    string op = varassign->op->getText();
    shared_ptr<Expr> rhs(expr(varassign->expression()));
    if (!rhs)
        cerr << "var binding unhandled rhs: " << varassign->expression()->getText() << endl;
    return shared_ptr<Stmt>(new VarAssignStmt(lhs, op, rhs));
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ModuleinstContext *moduleinst) {
    string varName = moduleinst->lowerCaseIdentifier()->getText();
    shared_ptr<BSVType> varType;
    if (moduleinst->t)
        varType = TypeChecker::bsvtype(moduleinst->t);
    else
        varType.reset(new BSVType());
    shared_ptr<Expr> rhs(expr(moduleinst->rhs));
    //FIXME: mark it as module instantiation?
    shared_ptr<Stmt> actionBindingStmt(new ActionBindingStmt(varType, varName, rhs));
    return actionBindingStmt;
}

std::shared_ptr<Pattern> GenerateAst::generateAst(BSVParser::PatternContext *ctx) {
    if (BSVParser::ConstantpatternContext *constPattern = ctx->constantpattern()) {
        if (constPattern->IntLiteral()) {
            return IntPattern::create(strtoul(ctx->getText().c_str(), 0, 0));
        } else if (constPattern->IntPattern()) {
            return make_shared<IntPattern>(ctx->getText());
        } else {
            fprintf(stderr, "Unhandled constant pattern: %s\n", ctx->getText().c_str());
            return WildcardPattern::create();
        }
    } else if (BSVParser::TaggedunionpatternContext *taggedPattern = ctx->taggedunionpattern()) {
        fprintf(stderr, "checkme tagged union pattern: %s\n", ctx->getText().c_str());
        return make_shared<TaggedPattern>(ctx->getText());
    } else if (BSVParser::TuplepatternContext *tuplePattern = ctx->tuplepattern()) {
        fprintf(stderr, "Unhandled tagged union pattern: %s\n", ctx->getText().c_str());
        vector<BSVParser::PatternContext *>patterns = ctx->tuplepattern()->pattern();
        vector<shared_ptr<Pattern>> ast_patterns;
        for (int i = 0; i < patterns.size(); i++)
            ast_patterns.push_back(generateAst(patterns[i]));
        return make_shared<TuplePattern>(ast_patterns);
    } else if (ctx->var) {
        return VarPattern::create(ctx->getText());
    } else if (ctx->pattern()) {
        return generateAst(ctx->pattern());
    } else {
        return WildcardPattern::create();
    }
    assert(0);
}


string GenerateAst::sourceLocation(antlr4::ParserRuleContext *ctx) {
    antlr4::Token *start = ctx->getStart();
    string filename = start->getTokenSource()->getSourceName();
    size_t line = start->getLine();
    return filename + ":" + to_string(line);
}
