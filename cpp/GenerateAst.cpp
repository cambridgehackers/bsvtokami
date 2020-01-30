#include "GenerateAst.h"

using namespace std;

class GenerateAstPackageVisitor : public DeclarationVisitor {
    ostream &logstream;
    vector<shared_ptr<Stmt>> &stmts;
public:
    GenerateAstPackageVisitor(ostream &logstream, vector<shared_ptr<Stmt>> &stmts) : logstream(logstream), stmts(stmts) {}

    void visitEnumDeclaration(const shared_ptr<EnumDeclaration> &decl) override {
        string name = decl->name;
        vector<string> members;
        for (int i = 0; i < decl->members.size(); i++)
            members.push_back(decl->members[i]->name);
        shared_ptr<Stmt> stmt = make_shared<TypedefEnumStmt>(decl->package, name, decl->bsvtype, members, decl->sourcePos);
        stmts.push_back(stmt);
    }

    void visitFunctionDefinition(const shared_ptr<FunctionDefinition> &decl) override {
        DeclarationVisitor::visitFunctionDefinition(decl);
    }

    void visitInterfaceDeclaration(const shared_ptr<InterfaceDeclaration> &decl) override {
        DeclarationVisitor::visitInterfaceDeclaration(decl);
    }

    void visitMethodDefinition(const shared_ptr<MethodDefinition> &decl) override {
        DeclarationVisitor::visitMethodDefinition(decl);
    }

    void visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl) override {
        DeclarationVisitor::visitMethodDeclaration(decl);
    }

    void visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl) override {
        DeclarationVisitor::visitModuleDefinition(decl);
    }

    void visitStructDeclaration(const shared_ptr<StructDeclaration> &decl) override {
        string name(decl->name);
        shared_ptr<BSVType> structType(decl->bsvtype);
        logstream << "struct " << structType->to_string() << endl;
        vector<string> memberNames;
        vector<shared_ptr<BSVType>> memberTypes;
        for (size_t i = 0; i < decl->members.size(); i++) {
            memberNames.push_back(decl->members[i]->name);
            memberTypes.push_back(decl->members[i]->bsvtype);
        }
        shared_ptr<TypedefStructStmt> stmt = make_shared<TypedefStructStmt>(decl->package, name, structType, memberNames, memberTypes, decl->sourcePos);
        stmts.push_back(stmt);
    }

    void visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl) override {
        shared_ptr<Stmt> stmt = make_shared<TypedefSynonymStmt>(decl->package, decl->bsvtype, decl->lhstype, decl->sourcePos);
        //stmt->prettyPrint(cout, 0);
        stmts.push_back(stmt);
    }

    void visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl) override {
        DeclarationVisitor::visitUnionDeclaration(decl);
    }
};

std::shared_ptr<LValue> GenerateAst::lvalue(BSVParser::LvalueContext *lhs) {
    if (lhs->exprprimary() != nullptr) {
        shared_ptr<Expr> lhsLValue(expr(lhs->exprprimary()));
        if (lhs->index != nullptr) {
            return make_shared<ArraySubLValue>(lhsLValue, expr(lhs->index));
        } else if (lhs->msb != nullptr) {
            return make_shared<RangeSelLValue>(lhsLValue, expr(lhs->msb), expr(lhs->lsb));
        } else {
            return make_shared<FieldLValue>(lhsLValue, lhs->lowerCaseIdentifier()->getText());
        }
    } else {
        shared_ptr<BSVType> bsvtype = typeChecker->lookup(lhs->lowerCaseIdentifier());
        shared_ptr<LValue> lvalue = make_shared<VarLValue>(lhs->lowerCaseIdentifier()->getText(), bsvtype);
        return lvalue;
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
        logstream << "Unhandled matches expr " << ctx->getText() << endl;
        return expr(matchesExpr);
    } else if (BSVParser::CaseexprContext *caseexpr = dynamic_cast<BSVParser::CaseexprContext *>(ctx)) {
        logstream << "Unhandled case expr " << ctx->getText() << endl;
        return result;
    }
    logstream << "How did we get here: expr " << ctx->getRuleIndex() << " " << ctx->getText() << endl;
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
        logstream << "Funny cond expr: " << ctx->getText() << endl;
        logstream << (bool) condexpr << (bool) thenexpr << (bool) elseexpr << endl;
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
        return make_shared<MatchesExpr>(lhs, pattern, exprs, sourcePos(ctx));
    } else {
        return make_shared<MatchesExpr>(lhs, pattern, sourcePos(ctx));
    }
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::BinopexprContext *ctx) {
    if (ctx->unopexpr()) {
        return expr(ctx->unopexpr());
    }
    shared_ptr<Expr> lhs(expr(ctx->left));
    shared_ptr<Expr> rhs(expr(ctx->right));
    string op(ctx->op->getText());
    if (!lhs) {
        cerr << "GenerateAst no lhs " << sourceLocation(ctx) << endl;
    }
    shared_ptr<Expr> result(new OperatorExpr(op, lhs, rhs));
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::UnopexprContext *ctx) {
    shared_ptr<Expr> result;
    shared_ptr<Expr> arg(expr(ctx->exprprimary()));
    if (ctx->op) {
        if (!arg)
            logstream << "unhandled unop expr: " << ctx->exprprimary()->getText() << endl;
        result.reset(new OperatorExpr(ctx->op->getText(), arg));
    } else {
        result = arg;
    }
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::ExprprimaryContext *ctx) {
    shared_ptr<Expr> result;
    shared_ptr<BSVType> resultType = typeChecker->lookup(ctx);

    if (BSVParser::FieldexprContext *fieldexpr = dynamic_cast<BSVParser::FieldexprContext *>(ctx)) {
        return expr(fieldexpr);
    } else if (BSVParser::VarexprContext *varexpr = dynamic_cast<BSVParser::VarexprContext *>(ctx)) {
	    return make_shared<VarExpr>(varexpr->getText(), resultType, sourcePos(ctx));
    } else if (BSVParser::IntliteralContext *intliteral = dynamic_cast<BSVParser::IntliteralContext *>(ctx)) {
        return make_shared<IntConst>(intliteral->getText(), sourcePos(ctx));
    } else if (BSVParser::StringliteralContext *stringliteral = dynamic_cast<BSVParser::StringliteralContext *>(ctx)) {
        return make_shared<StringConst>(stringliteral->getText(), sourcePos(ctx));
    } else if (BSVParser::ValueofexprContext *valueofexpr = dynamic_cast<BSVParser::ValueofexprContext *>(ctx)) {
        shared_ptr<BSVType> bsvtype = typeChecker->lookup(valueofexpr->bsvtype());
        return make_shared<ValueofExpr>(bsvtype, sourcePos(ctx));
    } else if (BSVParser::BitconcatContext *bitconcat = dynamic_cast<BSVParser::BitconcatContext *>(ctx)) {
        vector<shared_ptr<Expr>> values;
        for (int i = 0; bitconcat->expression(i); i++) {
            values.push_back(expr(bitconcat->expression(i)));
        }
        return make_shared<BitConcatExpr>(values, typeChecker->lookup(ctx), sourcePos(ctx));
    } else if (BSVParser::ArraysubContext *arraysub = dynamic_cast<BSVParser::ArraysubContext *>(ctx)) {
        shared_ptr<Expr> array(expr(arraysub->array));
        shared_ptr<Expr> msb(expr(arraysub->msb));
        if (arraysub->lsb) {
            shared_ptr<Expr> lsb(expr(arraysub->lsb));
            return make_shared<BitSelExpr>(array, msb, lsb, sourcePos(ctx));
        } else {
            return make_shared<ArraySubExpr>(array, msb, sourcePos(ctx));
        }
    } else if (BSVParser::CallexprContext *callexpr = dynamic_cast<BSVParser::CallexprContext *>(ctx)) {
        shared_ptr<Expr> function(expr(callexpr->fcn));
        vector<BSVParser::ExpressionContext *> args = callexpr->expression();
        vector<shared_ptr<Expr>> exprs;
        for (size_t i = 0; i < args.size(); i++) {
            exprs.push_back(expr(args.at(i)));
        }
        return make_shared<CallExpr>(function, exprs, sourcePos(ctx));
    } else if (BSVParser::SyscallexprContext *syscallexpr = dynamic_cast<BSVParser::SyscallexprContext *>(ctx)) {
        //FIXME: placeholder type for $display etc.
        shared_ptr<VarExpr> function = make_shared<VarExpr>(syscallexpr->fcn->getText(), make_shared<BSVType>(), sourcePos(ctx));
        vector<BSVParser::ExpressionContext *> args = syscallexpr->expression();
        vector<shared_ptr<Expr>> exprs;
        for (size_t i = 0; i < args.size(); i++) {
            exprs.push_back(expr(args.at(i)));
        }
        return make_shared<CallExpr>(function, exprs, sourcePos(ctx));
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
            logstream << "unhandled tagged union: " << unionexpr->getText() << endl;
        }
        shared_ptr<BSVType> bsvtype = typeChecker->lookup(ctx);
        return make_shared<EnumUnionStructExpr>(tag, keys, vals, bsvtype, sourcePos(ctx));
    } else if (BSVParser::ParenexprContext *parenexpr = dynamic_cast<BSVParser::ParenexprContext *>(ctx)) {
        return expr(parenexpr->expression());
    } else if (BSVParser::UndefinedexprContext *undef = dynamic_cast<BSVParser::UndefinedexprContext *>(ctx)) {
        //FIXME:: get type from type checker
        return make_shared<VarExpr>("Undefined", make_shared<BSVType>(), sourcePos(ctx));
    } else if (BSVParser::InterfaceexprContext *ifcexpr = dynamic_cast<BSVParser::InterfaceexprContext *>(ctx)) {
        shared_ptr<BSVType> bsvtype = typeChecker->lookup(ifcexpr);
        return make_shared<InterfaceExpr>(bsvtype, sourcePos(ifcexpr));
    } else {
        logstream << "Unhandled expr primary " << ctx->getText() << endl;
    }
    return result;
}

shared_ptr<Expr> GenerateAst::expr(BSVParser::FieldexprContext *fieldexpr) {
    string fieldName = fieldexpr->field->getText();
    shared_ptr<BSVType> resultType = typeChecker->lookup(fieldexpr);
    shared_ptr<BSVType> objType = typeChecker->lookup(fieldexpr->exprprimary());
    shared_ptr<Expr> object(expr(fieldexpr->exprprimary()));
    assert(!objType->isVar);
    shared_ptr<Declaration> objTypeDecl = typeChecker->lookup(objType->name);
    logstream << "field expr name " << objType->name << endl;
    shared_ptr<InterfaceDeclaration> interfaceDecl;
    shared_ptr<StructDeclaration> structDeclaration;
    if (objTypeDecl) {
        logstream << "objtypedecl " << objTypeDecl->name << endl;
        interfaceDecl = objTypeDecl->interfaceDeclaration();
        structDeclaration = objTypeDecl->structDeclaration();
    }
    if (!objTypeDecl || structDeclaration) {
        string fieldName = fieldexpr->field->getText();
        //if (fieldName == "tpl_1")
            logstream << "field expr type " << object->bsvtype->to_string() << " result type "
                      << resultType->to_string() << endl;
        return make_shared<FieldExpr>(object, fieldName, resultType, sourcePos(fieldexpr));
    } else {
        assert(interfaceDecl);
        logstream << "interfacedecl " << interfaceDecl->name << endl;
        shared_ptr<Declaration> fieldDecl = interfaceDecl->lookupMember(fieldName);
        shared_ptr<InterfaceDeclaration> subinterfaceDecl = fieldDecl->interfaceDeclaration();
        if (subinterfaceDecl) {
            logstream << "    subinterface " << subinterfaceDecl->name << endl;
            return make_shared<SubinterfaceExpr>(object, fieldName, resultType, sourcePos(fieldexpr));
        } else {
            logstream << "    must be a method " << fieldName << endl;
            shared_ptr<Expr> methodExpr = make_shared<MethodExpr>(object, fieldName, resultType, sourcePos(fieldexpr));
            return methodExpr;
        }
    }
}

shared_ptr<PackageDefStmt> GenerateAst::generateAst(BSVParser::PackagedefContext *ctx) {
    vector<BSVParser::PackagestmtContext *> stmts = ctx->packagestmt();

    vector<shared_ptr<Stmt>> package_stmts;
    logstream << "generateAst " << stmts.size() << " stmts" << endl;
    string packageName("<unnamed>");
    for (size_t i = 0; i < stmts.size(); i++) {
        if (ctx->packagedecl()) {
            packageName = ctx->packagedecl()->packageide()->getText();
        }
        antlrcpp::Any attributes = aiv.visit(stmts[i]);
        if (aiv.contains(attributes, "nogen")) {
            cerr << "Skipping (* nogen *) statement at " << sourceLocation(stmts[i]) << endl;
            continue;
        }
        generateAst(stmts[i], package_stmts);
    }
    return make_shared<PackageDefStmt>(packageName, package_stmts);
}

void GenerateAst::generateAst(BSVParser::PackagestmtContext *ctx, vector<shared_ptr<Stmt>> &stmts) {
    if (ctx->moduledef() != NULL) {
        stmts.push_back(generateAst(ctx->moduledef()));
    } else if (BSVParser::VarbindingContext *varbinding = ctx->varbinding()) {
        shared_ptr<Stmt> stmt = generateAst(varbinding);
        //stmt->prettyPrint(cout, 0);
        stmts.push_back(stmt);
    } else if (BSVParser::ImportdeclContext *importdecl = ctx->importdecl()) {
        //FIXME: package specifier
        string pkgname = importdecl->upperCaseIdentifier(0)->getText();
        shared_ptr<LexicalScope> packageScope = typeChecker->lookupPackage(pkgname);
        GenerateAstPackageVisitor packageVisitor(logstream, stmts);
        packageScope->visit(packageVisitor);
        shared_ptr<Stmt> stmt = make_shared<ImportStmt>(pkgname, sourcePos(ctx));
        //stmt->prettyPrint(cout, 0);
        stmts.push_back(stmt);
    } else if (BSVParser::InterfacedeclContext *interfacedecl = ctx->interfacedecl()) {
        shared_ptr<Stmt> stmt = generateAst(interfacedecl);
        //stmt->prettyPrint(cout, 0);
        stmts.push_back(stmt);
    } else if (BSVParser::TypedefenumContext *enumctx = ctx->typedefenum()) {
        shared_ptr<BSVType> bsvtype = make_shared<BSVType>(enumctx->upperCaseIdentifier()->getText());
        string name = bsvtype->name;
        vector<string> members;
        for (int i = 0; enumctx->typedefenumelement(i); i++) {
            members.push_back(enumctx->typedefenumelement(i)->upperCaseIdentifier()->getText());
        }
        shared_ptr<Stmt> stmt = make_shared<TypedefEnumStmt>(packageName, name, bsvtype, members, sourcePos(enumctx));
        stmts.push_back(stmt);
    } else if (BSVParser::TypedefsynonymContext *synonym = ctx->typedefsynonym()) {
        shared_ptr<BSVType> type(typeChecker->bsvtype(synonym->bsvtype()));
        shared_ptr<BSVType> typedeftype(typeChecker->bsvtype(synonym->typedeftype()));
        shared_ptr<Stmt> stmt = make_shared<TypedefSynonymStmt>(packageName, typedeftype, type, sourcePos(ctx));
        //stmt->prettyPrint(cout, 0);
        stmts.push_back(stmt);
    } else if (BSVParser::TypedefstructContext *def = ctx->typedefstruct()) {
        //FIXME: package name
        string name(def->typedeftype()->typeide()->getText());
        shared_ptr<BSVType> structType(typeChecker->bsvtype(def->typedeftype()));
        vector<BSVParser::StructmemberContext *> structmembers = def->structmember();
        vector<string> memberNames;
        vector<shared_ptr<BSVType>> memberTypes;
        for (size_t i = 0; i < structmembers.size(); i++) {
            BSVParser::StructmemberContext *member = structmembers[i];
            memberNames.push_back(member->lowerCaseIdentifier()->getText());
            memberTypes.push_back(typeChecker->bsvtype(member->bsvtype()));
        }
        shared_ptr<Stmt> stmt = make_shared<TypedefStructStmt>(packageName, name, structType, memberNames, memberTypes, sourcePos(ctx));
        //stmt->prettyPrint(cout, 0);
        stmts.push_back(stmt);
    } else if (BSVParser::FunctiondefContext *fcn = ctx->functiondef()) {
        shared_ptr<Stmt> stmt = generateAst(fcn);
        stmts.push_back(stmt);
    } else {
        logstream << "unhandled packagestmt" << ctx->getText() << endl;
    }
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::InterfacedeclContext *ctx) {
    string interfaceName(ctx->typedeftype()->typeide()->name->getText());
    logstream << "interfacedecl " << interfaceName.c_str() << endl;
    shared_ptr<BSVType> interfaceType(typeChecker->bsvtype(ctx->typedeftype()));
    vector<shared_ptr<Stmt>> ast_members;
    vector<BSVParser::InterfacememberdeclContext *> members = ctx->interfacememberdecl();
    for (size_t i = 0; i < members.size(); i++) {
        BSVParser::InterfacememberdeclContext *member = members[i];
        if (BSVParser::MethodprotoContext *methodproto = member->methodproto()) {
            string methodName(methodproto->lowerCaseIdentifier()->getText());
            shared_ptr<BSVType> returnType(typeChecker->bsvtype(methodproto->bsvtype()));
            vector<string> params;
            vector<shared_ptr<BSVType>> paramTypes;
            shared_ptr<Stmt> methoddecl = make_shared<MethodDeclStmt>(methodName, returnType, params, paramTypes, sourcePos(ctx));
            ast_members.push_back(methoddecl);

        }
    }

    shared_ptr<Stmt> interfacedecl = make_shared<InterfaceDeclStmt>(packageName, interfaceName, interfaceType, ast_members, sourcePos(ctx));
    return interfacedecl;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::SubinterfacedefContext *ctx) {
    string interfaceName(ctx->lowerCaseIdentifier(0)->getText());
    logstream << "subinterfacedef " << interfaceName << endl;
    shared_ptr<BSVType> interfaceType(
            new BSVType(ctx->lowerCaseIdentifier(0) ? ctx->lowerCaseIdentifier(0)->getText() : "<Interface TBD>"));
    vector<shared_ptr<Stmt>> ast_members;
    vector<BSVParser::InterfacestmtContext *> members = ctx->interfacestmt();
    for (size_t i = 0; i < members.size(); i++) {
        BSVParser::InterfacestmtContext *member = members[i];
        if (BSVParser::MethoddefContext *methoddef = member->methoddef()) {
            string methodName(methoddef->lowerCaseIdentifier(0)->getText());
            shared_ptr<BSVType> returnType(new BSVType());
            if (methoddef->bsvtype())
                returnType = typeChecker->bsvtype(methoddef->bsvtype());
            vector<string> params;
            vector<shared_ptr<BSVType>> paramTypes;
            shared_ptr<Stmt> methoddecl(new MethodDeclStmt(methodName, returnType, params, paramTypes, sourcePos(ctx)));
            ast_members.push_back(methoddecl);
        } else {
            logstream << "unhandled subinterface " << member->getText() << endl;
        }
    }

    shared_ptr<Stmt> interfacedef(new InterfaceDefStmt(string(), interfaceName, interfaceType, ast_members, sourcePos(ctx)));
    return interfacedef;
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ModuledefContext *ctx) {
    BSVParser::ModuleprotoContext *moduleproto = ctx->moduleproto();
    string moduleName(moduleproto->lowerCaseIdentifier()->getText());
    logstream << "moduledef " << moduleName << endl;
    shared_ptr<BSVType> interfaceType(typeChecker->bsvtype(moduleproto->bsvtype()));
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    BSVParser::ModuleprotoformalsContext *formals = ctx->moduleproto()->moduleprotoformals();
    if (formals) {
        vector<BSVParser::ModuleprotoformalContext *> formalvec = formals->moduleprotoformal();
        for (size_t i = 0; i < formalvec.size(); i++) {
            BSVParser::ModuleprotoformalContext *formal = formalvec.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            paramTypes.push_back(typeChecker->bsvtype(formal->bsvtype()));
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
                logstream << "Empty ast stmt for " << stmt->getText() << endl;
            ast_stmts.push_back(astStmt);
        } else if (BSVParser::SubinterfacedefContext *subinterfacedef = modstmt->subinterfacedef()) {
            ast_stmts.push_back(generateAst(subinterfacedef));
        } else {
            logstream << "Unhandled module stmt: " << modstmt->getText() << endl;
        }
    }
    shared_ptr<Stmt> moduledef = make_shared<ModuleDefStmt>(packageName, moduleName, interfaceType,
                                                            params, paramTypes,
                                                            ast_stmts, sourcePos(ctx));
    //moduledef->prettyPrint(cout, 0);
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
        returnType = typeChecker->bsvtype(proto->bsvtype());
    else
        returnType.reset(new BSVType("Void"));

    if (proto->methodformals()) {
        vector<BSVParser::MethodformalContext *> formals = proto->methodformals()->methodformal();
        for (size_t i = 0; i < formals.size(); i++) {
            BSVParser::MethodformalContext *formal = formals.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            if (formal->bsvtype() != nullptr) {
                paramTypes.push_back(typeChecker->bsvtype(formal->bsvtype()));
            } else {
                logstream << "functiondef formal with no type: "
                          << formal->getText()
                          << " at " << sourceLocation(formal)
                          << endl;
                paramTypes.push_back(shared_ptr<BSVType>(new BSVType()));

            }
        }
    }
    logstream << "    functiondef " << functionName << endl;
    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt) {
            logstream << "unhandled function stmt at " << sourceLocation(stmts.at(i)) << endl;
            logstream << "          " << stmts.at(i)->getText() << endl;
        }
        ast_stmts.push_back(stmt);
    }
    //FIXME: global?
    return make_shared<FunctionDefStmt>(packageName, functionName, returnType,
                                        params, paramTypes, guard, ast_stmts, sourcePos(ctx));
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::MethoddefContext *ctx) {
    string methodName(ctx->lowerCaseIdentifier(0)->getText());
    shared_ptr<BSVType> returnType(typeChecker->bsvtype(ctx->bsvtype()));
    vector<string> params;
    vector<shared_ptr<BSVType>> paramTypes;
    shared_ptr<Expr> guard;

    if (ctx->methodformals()) {
        vector<BSVParser::MethodformalContext *> formals = ctx->methodformals()->methodformal();
        for (size_t i = 0; i < formals.size(); i++) {
            BSVParser::MethodformalContext *formal = formals.at(i);
            params.push_back(formal->lowerCaseIdentifier()->getText());
            if (formal->bsvtype() != nullptr) {
                paramTypes.push_back(typeChecker->bsvtype(formal->bsvtype()));
            } else {
                logstream << "methoddef formal with no type: "
                          << formal->getText()
                          << " at " << sourceLocation(formal)
                          << endl;
                paramTypes.push_back(shared_ptr<BSVType>(new BSVType()));
            }
        }
    }
    logstream << "    methoddef " << methodName << endl;
    if (ctx->methodcond() != 0) {
        guard = expr(ctx->methodcond()->expression());
    }
    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt)
            logstream << "unhandled method stmt: " << stmts.at(i)->getText() << endl;
        ast_stmts.push_back(stmt);
    }
    return make_shared<MethodDefStmt>(methodName, returnType,
                                      params, paramTypes, guard, ast_stmts, sourcePos(ctx));
}

std::shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::RuledefContext *ctx) {
    string ruleName(ctx->lowerCaseIdentifier(0)->getText());
    logstream << "    ruledef " << ruleName << endl;
    shared_ptr<Expr> guard;
    if (ctx->rulecond() != 0) {
        logstream << "      when " << ctx->rulecond()->getText() << endl;
        guard = expr(ctx->rulecond()->expression());
    }

    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    vector<shared_ptr<Stmt>> ast_stmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(generateAst(stmts.at(i)));
        if (!stmt)
            logstream << "unhandled rule stmt: " << stmts.at(i)->getText();
        ast_stmts.push_back(stmt);
    }
    shared_ptr<RuleDefStmt> ruledef(new RuleDefStmt(ruleName, guard, ast_stmts, sourcePos(ctx)));
    return ruledef;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::StmtContext *ctx) {
    logstream << "        stmt " << ctx->getText() << endl;
    if (BSVParser::RegwriteContext *regwrite = ctx->regwrite()) {
        string regName(regwrite->lhs->getText());
        shared_ptr<Expr> rhs(expr(regwrite->rhs));
        shared_ptr<BSVType> regType = typeChecker->lookup(regwrite->rhs);
        shared_ptr<BSVType> elementType;
        if (!regType->isVar && regType->name == "Reg") {
            elementType = regType->params[0];
        } else {
            logstream << "(* Unhandled RegWrite element type " << regType->to_string() << " for regwrite: "
                      << ctx->getText() << "*)" << endl;
            elementType = make_shared<BSVType>("Bit", make_shared<BSVType>("32", BSVType_Numeric, false));
        }
        return make_shared<RegWriteStmt>(regName, elementType, rhs);
    } else if (BSVParser::VarbindingContext *varbinding = ctx->varbinding()) {
        return generateAst(varbinding);
    } else if (BSVParser::ActionbindingContext *actionbinding = ctx->actionbinding()) {
        return generateAst(actionbinding);
    } else if (BSVParser::VarassignContext *varassign = ctx->varassign()) {
        shared_ptr<Stmt> stmt = generateAst(varassign);
        //stmt->prettyPrint(cout, 0);
        return stmt;
    } else if (BSVParser::IfstmtContext *ifstmt = ctx->ifstmt()) {
        shared_ptr<Expr> condition(expr(ifstmt->expression()));
        shared_ptr<Stmt> thenStmt(generateAst(ifstmt->stmt(0)));
        shared_ptr<Stmt> elseStmt;
        if (ifstmt->stmt(1))
            elseStmt = generateAst(ifstmt->stmt(1));
        shared_ptr<IfStmt> ifStmt = make_shared<IfStmt>(condition, thenStmt, elseStmt, sourcePos(ctx));
        logstream << "if stmt at " << ifStmt->sourcePos.toString() << endl;
        logstream << "    assigned vars " << to_string(ifStmt->attrs().assignedVars) << endl;
        return ifStmt;
    } else if (BSVParser::BeginendblockContext *block = ctx->beginendblock()) {
        vector<BSVParser::StmtContext *> stmts = block->stmt();
        vector<shared_ptr<Stmt>> ast_stmts;
        for (size_t i = 0; i < stmts.size(); i++) {
            shared_ptr<Stmt> ast_stmt(generateAst(stmts.at(i)));
            if (!ast_stmt)
                logstream << "unhandled block stmt: " << stmts.at(i)->getText() << endl;
            ast_stmts.push_back(ast_stmt);
        }
        return make_shared<BlockStmt>(ast_stmts, sourcePos(ctx));
    } else if (BSVParser::ActionblockContext *block = ctx->actionblock()) {
        vector<BSVParser::StmtContext *> stmts = block->stmt();
        vector<shared_ptr<Stmt>> ast_stmts;
        for (size_t i = 0; i < stmts.size(); i++) {
            shared_ptr<Stmt> ast_stmt(generateAst(stmts.at(i)));
            if (!ast_stmt)
                logstream << "unhandled block stmt: " << stmts.at(i)->getText() << endl;
            ast_stmts.push_back(ast_stmt);
        }
        return make_shared<BlockStmt>(ast_stmts, sourcePos(ctx));
    } else if (BSVParser::ActionvalueblockContext *block = ctx->actionvalueblock()) {
        vector<BSVParser::StmtContext *> stmts = block->stmt();
        vector<shared_ptr<Stmt>> ast_stmts;
        for (size_t i = 0; i < stmts.size(); i++) {
            shared_ptr<Stmt> ast_stmt(generateAst(stmts.at(i)));
            if (!ast_stmt)
                logstream << "unhandled block stmt: " << stmts.at(i)->getText() << endl;
            ast_stmts.push_back(ast_stmt);
        }
        return make_shared<BlockStmt>(ast_stmts, sourcePos(ctx));
    } else if (BSVParser::PatternbindingContext *patternBinding = ctx->patternbinding()) {
        shared_ptr<Expr> val(expr(patternBinding->expression()));
        shared_ptr<Pattern> pat = generateAst(patternBinding->pattern());
        return make_shared<PatternMatchStmt>(pat, patternBinding->op->getText(), val);
    } else if (BSVParser::ReturnstmtContext *ret_stmt = ctx->returnstmt()) {
        shared_ptr<Expr> val(expr(ret_stmt->expression()));
        if (!val) {
            logstream << "Unhandled return stmt at " << sourceLocation(ret_stmt->expression()) << endl;
        }
        return make_shared<ReturnStmt>(val, sourcePos(ctx));
    } else if (BSVParser::ExpressionContext *exp_stmt = ctx->expression()) {
        shared_ptr<Expr> val(expr(exp_stmt));
        return make_shared<ExprStmt>(val, sourcePos(ctx));
    } else if (BSVParser::RuledefContext *ruledef = ctx->ruledef()) {
        return generateAst(ruledef);
    } else if (BSVParser::FunctiondefContext *fcn = ctx->functiondef()) {
        logstream << "function stmt " << ctx->getText() << endl;
        return generateAst(fcn);
    } else {
        logstream << "Unhandled stmt: " << ctx->getText() << endl;
        shared_ptr<Stmt> stmt;
        return stmt;
        //return make_shared<Stmt>(InvalidStmtType, sourcePos(ctx));
    }
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::VarbindingContext *varbinding) {
    std::vector<BSVParser::VarinitContext *> varinits = varbinding->varinit();
    for (size_t i = 0; i < varinits.size(); i++) {
        BSVParser::VarinitContext *varinit = varinits[i];
        string varName = varinit->lowerCaseIdentifier()->getText();
        shared_ptr<BSVType> varType = typeChecker->lookup(varinit->var);
        if (!varinit->rhs) {
            cerr << "varinit with no rhs at " << sourceLocation(varinit) << endl;
            cerr << "    " << varinit->getText() << endl;
        }
        assert(varinit->rhs);
        shared_ptr<Expr> rhs(expr(varinit->rhs));
        if (!rhs)
            logstream << "Unhandled var binding rhs at " << sourceLocation(varinit->expression()) << endl;
        return make_shared<VarBindingStmt>(varType, varName, rhs, sourcePos(varbinding));
    }
    //FIXME: how to make multiple bindings?
    assert(0);
    shared_ptr<Stmt> stmt;
    return stmt;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ActionbindingContext *actionbinding) {
    string varName = actionbinding->lowerCaseIdentifier()->getText();
    shared_ptr<BSVType> varType;
    if (actionbinding->t)
        varType = typeChecker->bsvtype(actionbinding->t);
    else
        varType.reset(new BSVType());
    shared_ptr<Expr> rhs(expr(actionbinding->rhs));

    //cout << "action binding rhs ";
    //expr(actionbinding->rhs)->prettyPrint(cout, 0); cout << endl;

    shared_ptr<Stmt> actionBindingStmt = make_shared<ActionBindingStmt>(varType, varName, rhs, sourcePos(actionbinding));
    return actionBindingStmt;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::VarassignContext *varassign) {
    shared_ptr<LValue> lhs(lvalue(varassign->lvalue(0)));
    string op = varassign->op->getText();
    shared_ptr<Expr> rhs(expr(varassign->expression()));
    if (!rhs)
        logstream << "var binding unhandled rhs: " << varassign->expression()->getText() << endl;
    shared_ptr<Stmt> stmt = make_shared<VarAssignStmt>(lhs, op, rhs, sourcePos(varassign));
    logstream << "var assign at " << stmt->sourcePos.toString() << endl;
    logstream << "    assigned vars " << to_string(stmt->attrs().assignedVars) << endl;
    return stmt;
}

shared_ptr<Stmt> GenerateAst::generateAst(BSVParser::ModuleinstContext *moduleinst) {
    string varName = moduleinst->lowerCaseIdentifier()->getText();
    shared_ptr<BSVType> varType;
    if (moduleinst->t)
        varType = typeChecker->bsvtype(moduleinst->t);
    else
        varType.reset(new BSVType());
    shared_ptr<Expr> rhs(expr(moduleinst->rhs));
    //FIXME: mark it as module instantiation?
    shared_ptr<Stmt> actionBindingStmt = make_shared<ActionBindingStmt>(varType, varName, rhs, sourcePos(moduleinst));
    return actionBindingStmt;
}

std::shared_ptr<Pattern> GenerateAst::generateAst(BSVParser::PatternContext *ctx) {
    if (BSVParser::ConstantpatternContext *constPattern = ctx->constantpattern()) {
        if (constPattern->IntLiteral()) {
            return make_shared<IntPattern>(strtoul(ctx->getText().c_str(), 0, 0));
        } else if (constPattern->IntPattern()) {
            return make_shared<IntPattern>(ctx->getText());
        } else {
            logstream << "Unhandled constant pattern: " << ctx->getText() << endl;
            return make_shared<WildcardPattern>();
        }
    } else if (BSVParser::TaggedunionpatternContext *taggedPattern = ctx->taggedunionpattern()) {
        logstream << "checkme tagged union pattern: " << ctx->getText() << endl;
        return make_shared<TaggedPattern>(ctx->getText());
    } else if (BSVParser::TuplepatternContext *tuplePattern = ctx->tuplepattern()) {
        logstream << "Unhandled tagged union pattern: " << ctx->getText() << endl;
        vector<BSVParser::PatternContext *> patterns = ctx->tuplepattern()->pattern();
        vector<shared_ptr<Pattern>> ast_patterns;
        for (int i = 0; i < patterns.size(); i++)
            ast_patterns.push_back(generateAst(patterns[i]));
        return make_shared<TuplePattern>(ast_patterns);
    } else if (ctx->var) {
        return make_shared<VarPattern>(ctx->getText());
    } else if (ctx->pattern()) {
        return generateAst(ctx->pattern());
    } else {
        return make_shared<WildcardPattern>();
    }
    assert(0);
}


string GenerateAst::sourceLocation(antlr4::ParserRuleContext *ctx) {
    antlr4::Token *start = ctx->getStart();
    string filename = start->getTokenSource()->getSourceName();
    size_t line = start->getLine();
    return filename + ":" + to_string(line);
}

SourcePos GenerateAst::sourcePos(antlr4::ParserRuleContext *ctx) {
    antlr4::Token *start = ctx->getStart();
    return SourcePos(start->getTokenSource()->getSourceName(), start->getLine(), start->getCharPositionInLine());
}
