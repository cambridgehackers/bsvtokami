

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include "BSVPreprocessor.h"
#include "TypeChecker.h"

PackageContext::PackageContext(const string &packageName)
    : packageName(packageName), logstream(string("kami/") + packageName + string(".sema.log"), ostream::out) {

}

const char *TypeChecker::check_result_name[] = {
        "unsat", "sat", "unknown"
};


string TypeChecker::searchIncludePath(const string &pkgName)
{
    for (int i = 0; i < includePath.size(); i++) {
        string candidate = includePath[i] + "/" + pkgName + ".bsv";
        int fd = open(candidate.c_str(), O_RDONLY);
        //logstream << "  candidate " << candidate << " fd " << fd << endl;
        if (fd >= 0) {
            close(fd);
            return candidate;
        }
    }
    return string();
}

void PackageContext::import(const shared_ptr<LexicalScope> &scope) {
    class PackageContextVisitor : public DeclarationVisitor {
        PackageContext *pc;
    public:
        PackageContextVisitor(PackageContext *pc) : pc(pc) {}
        void visitEnumDeclaration(const shared_ptr<EnumDeclaration> &decl) override {
            pc->visitEnumDeclaration(decl);
        }
        virtual void visitFunctionDefinition(const shared_ptr<FunctionDefinition> &decl) override {
            pc->logstream << "PackageContext::import visitFunctionDefinition " << decl->name << endl;
            pc->visitFunctionDefinition(decl);
        }

        void visitInterfaceDeclaration(const shared_ptr<InterfaceDeclaration> &decl) override {
            pc->visitInterfaceDeclaration(decl);
        }
        void visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl) override {
            pc->visitMethodDeclaration(decl);
        }
        void visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl) override {
            pc->visitModuleDefinition(decl);
        }
        void visitStructDeclaration(const shared_ptr<StructDeclaration> &decl) override{
            pc->visitStructDeclaration(decl);
        }
        void visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl) override {
            pc->visitTypeSynonymDeclaration(decl);
        }
        void visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl) override {
            pc->visitUnionDeclaration(decl);
        }
    } pcv(this);
    scope->visit(pcv);
}

void PackageContext::visitEnumDeclaration(const shared_ptr<EnumDeclaration> &decl) {
    logstream << "    visitEnumDeclaration " << decl->name << endl;
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
    for (int i = 0; i < decl->members.size(); i++) {
        shared_ptr<Declaration> tagdecl = decl->members[i];
        logstream << "        enum tag " << tagdecl->name << endl;
        enumtag.insert(make_pair(tagdecl->name, tagdecl->parent));
    }
}
void PackageContext::visitInterfaceDeclaration(const shared_ptr<InterfaceDeclaration> &decl) {
    logstream << "    visitInterfaceDeclaration " << decl->name << endl;
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
    for (auto it = decl->members.cbegin(); it != decl->members.cend(); ++it) {
        shared_ptr<Declaration> memberDecl = *it;
        memberDeclaration.emplace(memberDecl->name, memberDecl);
    }
}


void PackageContext::visitFunctionDefinition(const shared_ptr<FunctionDefinition> &decl) {
    declaration[decl->name] = decl;
    declarationList.push_back(decl);
}

void PackageContext::visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl) {
    assert(0);
}

void PackageContext::visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl) {
    declaration[decl->name] = decl;
    declarationList.push_back(decl);
}

void PackageContext::visitStructDeclaration(const shared_ptr<StructDeclaration> &decl) {
    logstream << "  imported struct type " << decl->name << " " << decl->bsvtype->to_string() << endl;
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
    for (int i = 0; i < decl->members.size(); i++) {
        shared_ptr<Declaration> member = decl->members[i];
        memberDeclaration.insert(make_pair(member->name, member));
    }
}

void PackageContext::visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl) {
    logstream << "  imported type synonym " << decl->name << " " << decl->bsvtype->to_string() << endl;
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
}

void PackageContext::visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl) {
    logstream << "package context union " << decl->name << endl;
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
    for (int i = 0; i < decl->members.size(); i++) {
        shared_ptr<Declaration> member = decl->members[i];
        logstream << "    union member " << member->name << endl;
        memberDeclaration.insert(make_pair(member->name, member));
        enumtag.insert(make_pair(member->name, decl));
    }
}



BSVParser::PackagedefContext *TypeChecker::analyzePackage(const string &packageName) {
    if (packageScopes.find(packageName) != packageScopes.cend())
        return nullptr;

    currentContext->logstream << "analyze package " << packageName << endl;

    shared_ptr<PackageContext> previousContext = currentContext;
    shared_ptr<LexicalScope> previousScope = lexicalScope;
    lexicalScope = make_shared<LexicalScope>(packageName);
    currentContext = make_shared<PackageContext>(packageName);
    setupModuleFunctionConstructors();

    //string inputFileName(argv[i]);
    string inputFileName = searchIncludePath(packageName);
    if (inputFileName.size() == 0)
        cerr << "No file found for import " << packageName << endl;
    assert(inputFileName.size());
    cerr << "Parsing imported file \"" << inputFileName << "\"" << endl;
    BSVPreprocessor preprocessor(inputFileName);
    preprocessor.define(definitions);
    CommonTokenStream tokens((TokenSource * ) & preprocessor);

    tokens.fill();
    bool dumptokens = false;
    if (dumptokens) {
        for (auto token : tokens.getTokens()) {
            std::cout << token->toString() << std::endl;
        }
    }

    BSVParser parser(&tokens);
    //parser.addErrorListener(&ConsoleErrorListener::INSTANCE);
    BSVParser::PackagedefContext *tree = parser.packagedef();
    packageScopes[packageName] = lexicalScope;

    visit(tree);

    currentContext->logstream.close();

    lexicalScope = previousScope;
    currentContext = previousContext;
    cerr << "returning to package " << currentContext->packageName << endl;
    return tree;
}

const vector<string> TypeChecker::visitedPackageNames() const {
    vector <string> result;
    for (auto it = packageScopes.cbegin(); it != packageScopes.cend(); ++it) {
        result.push_back(it->first);
    }
    return result;
}

shared_ptr<LexicalScope> TypeChecker::lookupPackage(const string &pkgname) {
    auto it = packageScopes.find(pkgname);
    if (it != packageScopes.cend()) {
        return it->second;
    }
    return shared_ptr<LexicalScope>();
}

void TypeChecker::setupModuleFunctionConstructors() {
    const string constructorNames[] = { "Function" };
    for (int c = 0; c < 1; c++) {
        string constructorPrefix = constructorNames[c];
        for (int arity = 1; arity < 20; arity++) {
            string constructorName = constructorPrefix + to_string(arity);
            vector<shared_ptr<BSVType>> paramTypes;
            for (int p = 0; p < arity; p++) {
                paramTypes.push_back(make_shared<BSVType>());
            }
            shared_ptr<BSVType> interfaceType = make_shared<BSVType>(constructorName, paramTypes);
            std::shared_ptr<Declaration> constructorDecl = make_shared<Declaration>("Prelude", constructorName, interfaceType,
                                                                                    GlobalBindingType);
            currentContext->logstream << "adding constructor: " << constructorName << endl;
            currentContext->typeDeclarationList.push_back(constructorDecl);
            currentContext->typeDeclaration[constructorName] = constructorDecl;
        }
    }
}

void TypeChecker::setupZ3Context() {
    currentContext->logstream << "setup Z3 context" << endl;
    exprs.clear();
    trackers.clear();
    typeDecls.clear();

    intSort = context.int_sort();
    boolSort = context.bool_sort();
    stringSort = context.string_sort();

    Z3_constructor bozo_con = Z3_mk_constructor(context,
                                                Z3_mk_string_symbol(context, "Bozo"),
                                                Z3_mk_string_symbol(context, "isBozo"),
                                                0, NULL, NULL, NULL);

    Z3_symbol numeric_field_names[] = {Z3_mk_string_symbol(context, "elt")};
    Z3_sort numeric_field_sorts[] = {intSort};
    unsigned numeric_field_sort_refs[] = {0};
    Z3_constructor numeric_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Numeric"),
                                               Z3_mk_string_symbol(context, "isNumeric"),
                                               1,
                                               numeric_field_names,
                                               numeric_field_sorts,
                                               numeric_field_sort_refs);

    Z3_symbol freevar_field_names[] = {Z3_mk_string_symbol(context, "var")};
    Z3_sort freevar_field_sorts[] = {stringSort};
    unsigned freevar_field_sort_refs[] = {0};
    Z3_constructor freevar_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "FreeVar"),
                                                   Z3_mk_string_symbol(context, "isFreeVar"),
                                                   1,
                                                   freevar_field_names,
                                                   freevar_field_sorts,
                                                   freevar_field_sort_refs);

    Z3_constructor default_constructors[] = {
            bozo_con,
            freevar_con,
            numeric_con
    };
    unsigned num_default_constructors = sizeof(default_constructors) / sizeof(default_constructors[0]);
    // constructors for user-defined types
    unsigned num_constructors = num_default_constructors + currentContext->typeDeclarationList.size();
    Z3_constructor *constructors = new Z3_constructor[num_constructors];

    for (int i = 0; i < num_default_constructors; i++)
        constructors[i] = default_constructors[i];

    for (int i = 0; i < currentContext->typeDeclarationList.size(); i++) {
        std::shared_ptr<Declaration> typeDecl(currentContext->typeDeclarationList[i]);
        std::shared_ptr<BSVType> interfaceType(typeDecl->bsvtype);
        int arity = interfaceType->params.size();
        std::string typePredicate(std::string("is_") + typeDecl->name);
        //cerr << "User defined type " << typeDecl->name << " arity " << arity << endl;

        Z3_symbol *param_symbols = new Z3_symbol[arity];
        Z3_sort *param_sorts = new Z3_sort[arity]; //(Z3_sort *)malloc(sizeof(Z3_sort) * arity);
        unsigned *sort_refs = new unsigned[arity];
        for (int j = 0; j < arity; j++) {
            shared_ptr<BSVType> paramType = interfaceType->params[j];
            param_symbols[j] = Z3_mk_string_symbol(context, paramType->name.c_str());
            param_sorts[j] = (Z3_sort)NULL;
            sort_refs[j] = 0;
        }
        constructors[i + num_default_constructors] = Z3_mk_constructor(context,
                                                                       Z3_mk_string_symbol(context,
                                                                                           typeDecl->name.c_str()),
                                                                       Z3_mk_string_symbol(context,
                                                                                           typePredicate.c_str()),
                //FIXME type parameters
                                                                       arity, param_symbols, param_sorts, sort_refs);
    }

    typeSort = z3::sort(context, Z3_mk_datatype(context, Z3_mk_string_symbol(context, "BSVType"),
                                                num_constructors,
                                                constructors));

    for (unsigned i = 0; i < num_constructors; i++) {
        Z3_func_decl func_decl = Z3_get_datatype_sort_constructor(context, typeSort, i);
        Z3_func_decl recognizer = Z3_get_datatype_sort_recognizer(context, typeSort, i);
        Z3_symbol name = Z3_get_decl_name(context, func_decl);
        //fprintf(stderr, "Constructor %d name is %s\n", i, Z3_get_symbol_string(context, name));
        // since no default constructor for z3::func_decl, use insert with a pair
        z3::func_decl func_decl_obj = z3::func_decl(context, func_decl);
        z3::func_decl func_recognizer_obj = z3::func_decl(context, recognizer);
        typeDecls.insert(std::pair<std::string, z3::func_decl>(Z3_get_symbol_string(context, name), func_decl_obj));
        typeRecognizers.insert(std::pair<std::string, z3::func_decl>(Z3_get_symbol_string(context, name), func_recognizer_obj));
        //fprintf(stderr, "               name is %s\n", func_decl_obj.name().str().c_str());
    }
    boolops["=="] = true;
    boolops["!="] = true;
    boolops["<"] = true;
    boolops[">"] = true;
    boolops["<="] = true;
    boolops[">="] = true;
    boolops["&&"] = true;
    boolops["||"] = true;
}

bool TypeChecker::checkSolution(antlr4::ParserRuleContext *ctx, bool displaySolution, bool showSolver) {
    //solver.push();
    z3::check_result checked = solver.check();
    currentContext->logstream << "  Type checking at " << sourceLocation(ctx) << ": " << check_result_name[checked] << endl;
    if (checked == z3::sat) {

        //bool displaySolution = false;
        if (displaySolution) {
            z3::model mod = solver.get_model();
            currentContext->logstream << "model: " << mod << endl;
            currentContext->logstream << exprs.size() << " exprs" << endl;
            for (auto it = exprs.cbegin(); it != exprs.cend(); ++it) {
                z3::expr e = it->second;
                try {
                    z3::expr v = mod.eval(e, true);
                    currentContext->logstream << e << " evaluates to " << v << " for " << it->first->getText() << " at "
                                              << sourceLocation(it->first) << endl;
                } catch (const exception &e) {
                    currentContext->logstream << "exception " << e.what() << " on expr: " << it->second << " @"
                                              << it->first->getRuleIndex()
                                              << " at " << sourceLocation(it->first) << endl;
                }
            }
        }
    } else {
        currentContext->logstream << solver << endl;
        z3::expr_vector unsat_core = solver.unsat_core();
        currentContext->logstream << "unsat_core " << unsat_core << endl;
        currentContext->logstream << "unsat_core.size " << unsat_core.size() << endl;
#ifdef FAIL_ON_UNSAT
        assert(0);
#endif
        return false;
    }
    //solver.pop();
    return true;
}

shared_ptr<BSVType> TypeChecker::modelValue(z3::expr e) {
    z3::model mod = solver.get_model();
    z3::expr v = mod.eval(e, true);
    return bsvtype(v, mod);
}




string TypeChecker::freshString(std::string name) {
    char uniq_name[128];
    snprintf(uniq_name, sizeof(uniq_name), "%s-%d", name.c_str(), nameCount++);
    return string(uniq_name);
}

z3::symbol TypeChecker::freshName(std::string name) {
    char uniq_name[128];
    snprintf(uniq_name, sizeof(uniq_name), "%s-%d", name.c_str(), nameCount++);
    return context.str_symbol(uniq_name);
}

z3::expr TypeChecker::freshConstant(std::string name, z3::sort sort) {
    return context.constant(freshName(name), sort);
}

z3::expr TypeChecker::constant(std::string name, z3::sort sort) {
    return context.constant(context.str_symbol(name.c_str()), sort);
}

void TypeChecker::insertExpr(antlr4::ParserRuleContext *ctx, z3::expr expr) {
    currentContext->logstream << "  insert expr " << ctx->getText().c_str() << " @" << ctx->getRuleIndex() << " at " << sourceLocation(ctx) << endl;
    exprs.insert(std::pair<antlr4::ParserRuleContext *, z3::expr>(ctx, expr));
}

void TypeChecker::addConstraint(z3::expr constraint, const string &trackerPrefix, antlr4::ParserRuleContext *ctx) {
    string trackerName(freshString(trackerPrefix));
    currentContext->logstream << "  insert tracker " << ctx->getText().c_str() << " prefix " << trackerName << " at " << sourceLocation(ctx) << endl;

    solver.add(constraint, trackerName.c_str());
    trackers.insert(std::pair<string, antlr4::ParserRuleContext *>(trackerName, ctx));
}

z3::expr TypeChecker::andExprs(std::vector<z3::expr> exprs) {
    assert(exprs.size() > 0);
    if (exprs.size() == 1) {
        return exprs.at(0);
    } else {
        z3::expr result = exprs.at(0);
        for (int i = 1; i < exprs.size(); i++) {
            result = (result && exprs[i]);
        }
        return result;
    }
}

z3::expr TypeChecker::orExprs(std::vector<z3::expr> exprs) {
    assert(exprs.size() > 0);
    if (exprs.size() == 1) {
        return exprs.at(0);
    } else {
        z3::expr result = exprs.at(0);
        for (int i = 1; i < exprs.size(); i++) {
            result = (result || exprs[i]);
        }
        return result;
    }
}


TypeChecker::TypeChecker(const string &packageName, const vector<string> &includePath,
                         const vector<string> &definitions)
        : context(), solver(context), typeSort(context), intSort(context), boolSort(context), stringSort(context), nameCount(100),
          actionContext(false),
          includePath(includePath), definitions(definitions) {
    //solver.set("produce-unsat-cores", true);
    z3::params p(context);
    // enable unsat core tracking
    p.set("unsat_core", true);
    solver.set(p);
    lexicalScope = make_shared<LexicalScope>("<global>");
    currentContext = make_shared<PackageContext>(packageName);
    currentContext->packageName = packageName;
    setupModuleFunctionConstructors();
}

TypeChecker::~TypeChecker() {}


shared_ptr<BSVType> TypeChecker::lookup(antlr4::ParserRuleContext *ctx) {
    if (exprTypes.find(ctx) != exprTypes.cend())
        return exprTypes.find(ctx)->second;
    currentContext->logstream << "no entry for @" << ctx->getRuleIndex() << ": " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
    return BSVType::create("NOENT");
}

shared_ptr<Declaration> TypeChecker::lookup(const string &varname, const string &packageName) {
    shared_ptr<Declaration> vardecl;
    if (packageName.size()) {
        vardecl = packageScopes[packageName]->lookup(varname);
        if (vardecl)
            currentContext->logstream << "found vardecl " << varname << " in package " << packageName << endl;
    } else {
        vardecl = lexicalScope->lookup(varname);
        if (!vardecl) {
            auto it = currentContext->declaration.find(varname);
            if (it != currentContext->declaration.cend())
                vardecl = it->second;
        }
        if (!vardecl) {
            auto it = currentContext->typeDeclaration.find(varname);
            if (it != currentContext->typeDeclaration.cend())
                vardecl = it->second;
        }
        if (vardecl)
            currentContext->logstream << "found global vardecl " << varname << " unique " << vardecl->uniqueName
                                      << endl;
    }
    return vardecl;
}

shared_ptr<BSVType> TypeChecker::dereferenceType(const shared_ptr<BSVType> &bsvtype) {
    if (bsvtype->isVar || bsvtype->isNumeric())
        return bsvtype;

    shared_ptr<BSVType> derefType = bsvtype;
    auto it = currentContext->typeDeclaration.find(bsvtype->name);
    if (it != currentContext->typeDeclaration.cend()) {
        shared_ptr<Declaration> decl = it->second;
        shared_ptr<TypeSynonymDeclaration> synonymDecl = decl->typeSynonymDeclaration();
        //currentContext->logstream << "dereferencing bsvtype " << bsvtype->name << " found " << decl->name << endl;
        if (synonymDecl) {
            currentContext->logstream << "dereferencing bsvtype " << bsvtype->name << " arity " << bsvtype->params.size() << endl;
            assert(synonymDecl->bsvtype->params.size() == 0);
            derefType = synonymDecl->lhstype;
            if (derefType->isNumeric())
                return derefType;
            vector<shared_ptr<BSVType>> derefParams;
            for (int i = 0; i < derefType->params.size(); i++)
                derefParams.push_back(dereferenceType(derefType->params[i]));
            derefType = dereferenceType(make_shared<BSVType>(derefType->name, derefParams));
        } else {

            if (bsvtype->params.size() == 0)
                return bsvtype;

            vector<shared_ptr<BSVType>> derefParams;
            for (int i = 0; i < bsvtype->params.size(); i++)
                derefParams.push_back(dereferenceType(bsvtype->params[i]));
            derefType = make_shared<BSVType>(bsvtype->name, derefParams);
        }
    }
    if (derefType->name == "TLog")
        currentContext->logstream << "computed type " << derefType->name << " kind " << derefType->kind << " numeric " << derefType->isNumeric() << " constant " << derefType->isConstant() << endl;
    if (derefType->isNumeric() && derefType->isConstant())
        return derefType->eval();

    return derefType;
}

string TypeChecker::sourceLocation(antlr4::ParserRuleContext *ctx) {
    antlr4::Token *start = ctx->getStart();
    string filename = start->getTokenSource()->getSourceName();
    size_t line = start->getLine();
    return filename + ":" + to_string(line);
}

SourcePos TypeChecker::sourcePos(antlr4::ParserRuleContext *ctx) {
    antlr4::Token *start = ctx->getStart();
    return SourcePos(start->getTokenSource()->getSourceName(), start->getLine(), start->getCharPositionInLine());
}

void TypeChecker::addDeclaration(BSVParser::PackagestmtContext *pkgstmt) {
    if (pkgstmt->interfacedecl()) {
        addDeclaration(pkgstmt->interfacedecl());
    } else if (pkgstmt->functiondef()) {
        addDeclaration(pkgstmt->functiondef());
    } else if (pkgstmt->moduledef()) {
        addDeclaration(pkgstmt->moduledef());
    } else if (pkgstmt->typeclassdecl()) {
        addDeclaration(pkgstmt->typeclassdecl());
    } else if (pkgstmt->typeclassinstance()) {
        addDeclaration(pkgstmt->typeclassinstance());
    } else if (pkgstmt->typedefenum()) {
        addDeclaration(pkgstmt->typedefenum());
    } else if (pkgstmt->typedefstruct()) {
        addDeclaration(pkgstmt->typedefstruct());
    } else if (pkgstmt->typedefsynonym()) {
        addDeclaration(pkgstmt->typedefsynonym());
    } else if (pkgstmt->typedeftaggedunion()) {
        addDeclaration(pkgstmt->typedeftaggedunion());
    } else if (pkgstmt->varbinding()) {
        addDeclaration(pkgstmt->varbinding());
    } else if (pkgstmt->importdecl()) {
        BSVParser::ImportdeclContext *importdecl = pkgstmt->importdecl();
        string pkgName = importdecl->upperCaseIdentifier(0)->getText();
        currentContext->logstream << "importing package " << pkgName << endl;

        analyzePackage(pkgName);
        shared_ptr<LexicalScope> pkgScope = packageScopes[pkgName];
        currentContext->import(pkgScope);

    } else if (pkgstmt->exportdecl()) {
        // handled later?
    } else {
        currentContext->logstream << "addDeclaration: unhandled package stmt at " << sourceLocation(pkgstmt) << endl;
        assert(0);
    }
}

void TypeChecker::addDeclaration(BSVParser::InterfacedeclContext *ctx) {
    setupZ3Context();

    shared_ptr<BSVType> interfaceType(bsvtype(ctx->typedeftype()));
    string name(interfaceType->name);

    int arity = interfaceType->params.size();

    currentContext->logstream << "add decl interface type : ";
    interfaceType->prettyPrint(currentContext->logstream);
    currentContext->logstream << " arity " << arity << endl;

    shared_ptr<InterfaceDeclaration> decl(new InterfaceDeclaration(currentContext->packageName, name, interfaceType, sourcePos(ctx)));
    currentContext->typeDeclarationList.push_back(decl);
    currentContext->typeDeclaration[name] = decl;
    lexicalScope->bind(name, decl);

    pushScope(name);
    auto members = ctx->interfacememberdecl();
    for (int i = 0; i < members.size(); i++) {
        shared_ptr<Declaration> memberDecl((Declaration *) visitInterfacememberdecl(members[i]));

        currentContext->logstream << " subinterface decl " << memberDecl->name << endl;
        currentContext->memberDeclaration.emplace(memberDecl->name, memberDecl);
        memberDecl->parent = decl;
        decl->members.push_back(memberDecl);
    }
    popScope();
}

void TypeChecker::addDeclaration(BSVParser::FunctiondefContext *functiondef) {
    if (!lexicalScope->isGlobal())
        return;
    BSVParser::FunctionprotoContext *functionproto = functiondef->functionproto();
    addDeclaration(functionproto);
}

void TypeChecker::addDeclaration(BSVParser::FunctionprotoContext *functionproto) {
    string functionName = functionproto->name->getText();
    shared_ptr<BSVType> functionType = bsvtype(functionproto);
    shared_ptr<FunctionDefinition> functionDecl = make_shared<FunctionDefinition>(currentContext->packageName,
                                                                                  functionName, functionType,
                                                                                  GlobalBindingType,
                                                                                  sourcePos(functionproto));
    lexicalScope->bind(functionName, functionDecl);
    currentContext->logstream << "addDeclaration function proto " << functionName << " at "
                              << sourceLocation(functionproto) << endl;
}

void TypeChecker::addDeclaration(BSVParser::ModuledefContext *module) {
    addDeclaration(module->moduleproto());

}

void TypeChecker::addDeclaration(BSVParser::ModuleprotoContext *moduleproto) {
    string moduleName = moduleproto->name->getText();
    currentContext->logstream << "add declaration module proto " << moduleName << endl;
    shared_ptr<BSVType> moduleType = bsvtype(moduleproto);
    lexicalScope->bind(moduleName, make_shared<ModuleDefinition>(currentContext->packageName, moduleName, moduleType, sourcePos(moduleproto)));
}

void TypeChecker::addDeclaration(BSVParser::OverloadeddeclContext *overloadeddecl) {
    if (overloadeddecl->functionproto()) {
        addDeclaration(overloadeddecl->functionproto());
    } else if (overloadeddecl->moduleproto()) {
        addDeclaration(overloadeddecl->moduleproto());
    } else if (overloadeddecl->varbinding()) {
        currentContext->logstream << "type class containing varbinding at " << sourceLocation(overloadeddecl) << endl;
        addDeclaration(overloadeddecl->varbinding());
    } else {
        assert(0);
    }
}

void TypeChecker::addDeclaration(BSVParser::TypeclassdeclContext *typeclassdecl) {
    currentContext->logstream << "visit type class decl " << typeclassdecl->typeclasside(0)->getText() << " at " << sourceLocation(typeclassdecl) << endl;
    for (int i = 0; typeclassdecl->overloadeddecl(i); i++) {
        addDeclaration(typeclassdecl->overloadeddecl(i));
    }
}

void TypeChecker::addDeclaration(BSVParser::TypeclassinstanceContext *typeclassinstance) {
    currentContext->logstream << "visit typeclass instance at " << sourceLocation(typeclassinstance) << endl;
}

void TypeChecker::addDeclaration(BSVParser::TypedefenumContext *ctx) {
    BSVParser::UpperCaseIdentifierContext *id = ctx->upperCaseIdentifier();
    string name(id->getText());
    shared_ptr<BSVType> bsvtype(new BSVType(name));
    shared_ptr<EnumDeclaration> decl(new EnumDeclaration(currentContext->packageName, name, bsvtype, sourcePos(ctx)));
    parentDecl = decl;
    lexicalScope->bind(name, decl);

    size_t numelts = ctx->typedefenumelement().size();
    for (size_t i = 0; i < numelts; i++) {
        BSVParser::TypedefenumelementContext *elt = ctx->typedefenumelement().at(i);
        if (elt) {
            currentContext->logstream << "enum elt " << elt->getText() << endl;
            shared_ptr<Declaration> subdecl = visit(elt);
            subdecl->parent = decl;
            decl->members.push_back(subdecl);
        }
    }
    currentContext->visitEnumDeclaration(decl);
}

void TypeChecker::addDeclaration(BSVParser::TypedefstructContext *structdef) {
    shared_ptr<BSVType> typedeftype(bsvtype(structdef->typedeftype()));
    string name = typedeftype->name;
    currentContext->logstream << "visit typedef struct " << name << endl;
    shared_ptr<StructDeclaration> structDecl = make_shared<StructDeclaration>(currentContext->packageName, name, typedeftype, sourcePos(structdef));
    for (int i = 0; structdef->structmember(i); i++) {
        shared_ptr<Declaration> subdecl = visit(structdef->structmember(i));
        structDecl->members.push_back(subdecl);
        subdecl->parent = structDecl;
    }
    currentContext->visitStructDeclaration(structDecl);
    lexicalScope->bind(name, structDecl);
}

void TypeChecker::addDeclaration(BSVParser::TypedefsynonymContext *synonymdef) {
    shared_ptr<BSVType> lhstype = bsvtype(synonymdef->bsvtype());
    shared_ptr<BSVType> typedeftype = bsvtype(synonymdef->typedeftype());
    currentContext->logstream << "visit typedef synonym " << typedeftype->name << endl;
    shared_ptr<TypeSynonymDeclaration> synonymDecl = make_shared<TypeSynonymDeclaration>(currentContext->packageName, typedeftype->name,
                                                                                         lhstype, typedeftype, sourcePos(synonymdef));
    currentContext->typeDeclaration[typedeftype->name] = synonymDecl;
    currentContext->typeDeclarationList.push_back(synonymDecl);
    lexicalScope->bind(typedeftype->name, synonymDecl);
}

void TypeChecker::addDeclaration(BSVParser::TypedeftaggedunionContext *uniondef) {
    shared_ptr<BSVType> typedeftype(bsvtype(uniondef->typedeftype()));
    string name = typedeftype->name;
    shared_ptr<UnionDeclaration> unionDecl =  make_shared<UnionDeclaration>(name, typedeftype, sourcePos(uniondef));
    currentContext->logstream << "add declaration typedef union " << name << endl;
    for (int i = 0; uniondef->unionmember(i); i++) {
        shared_ptr<Declaration> subdecl = visit(uniondef->unionmember(i));
        unionDecl->members.push_back(subdecl);
    }
    currentContext->visitUnionDeclaration(unionDecl);
    shared_ptr<Declaration> decl = unionDecl;
    lexicalScope->bind(name, decl);
}


void TypeChecker::addDeclaration(BSVParser::VarbindingContext *varbinding) {
    currentContext->logstream << "add declaration varbinding " << varbinding->varinit(0)->getText() << endl;
    assert(varbinding->t);
    shared_ptr<BSVType> varType = bsvtype(varbinding->t);
    BindingType bindingType = (lexicalScope->isGlobal() ? GlobalBindingType : LocalBindingType);
    string packageName = (lexicalScope->isGlobal() ? currentContext->packageName : string());
    for (int i = 0; varbinding->varinit(i); ++i) {
        BSVParser::VarinitContext *varinit = varbinding->varinit(i);
        string varName = varinit->lowerCaseIdentifier()->getText();
        lexicalScope->bind(varName, make_shared<Declaration>(packageName, varName, varType, bindingType));
    }
}

antlrcpp::Any TypeChecker::visitPackagedef(BSVParser::PackagedefContext *ctx) {
    currentContext->logstream << "importing Prelude " << endl;
    analyzePackage("Prelude");
    shared_ptr<LexicalScope> pkgScope = packageScopes["Prelude"];
    currentContext->import(pkgScope);

    if (ctx->packagedecl())
        visit(ctx->packagedecl());

    for (size_t i = 0; ctx->packagestmt(i); i++) {
        addDeclaration(ctx->packagestmt(i));
    }

    for (size_t i = 0; ctx->packagestmt(i); i++) {
        visit(ctx->packagestmt(i));
    }
    return freshConstant("pkgstmt", typeSort);
}

antlrcpp::Any TypeChecker::visitPackagedecl(BSVParser::PackagedeclContext *ctx) {
    setupZ3Context();
    return freshConstant("pkgdecl", typeSort);
}

antlrcpp::Any TypeChecker::visitEndpackage(BSVParser::EndpackageContext *ctx) {
    return freshConstant("endpkg", typeSort);
}

antlrcpp::Any TypeChecker::visitLowerCaseIdentifier(BSVParser::LowerCaseIdentifierContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    string varname(ctx->getText());
    shared_ptr<Declaration> vardecl = lookup(varname);
    shared_ptr<FunctionDefinition> functionDef = vardecl->functionDefinition();
    string uniqueName = (vardecl) ? vardecl->uniqueName : varname;
    if (functionDef) {
        uniqueName = freshString(varname);
        shared_ptr<BSVType> uniqueType = freshType(functionDef->bsvtype);
        z3::expr uniqueExpr = bsvTypeToExpr(uniqueType);
        addConstraint(constant(uniqueName, typeSort) == uniqueExpr, uniqueName + "$trk", ctx);
        currentContext->logstream << "visitLowerCaseIdentifier " << (constant(uniqueName, typeSort) == uniqueExpr) << endl;
    }
    if (!vardecl)
        currentContext->logstream << "No decl found for var " << varname << " at " << sourceLocation(ctx) << endl;
    assert(vardecl);
    z3::expr varExpr = constant(uniqueName, typeSort);
    insertExpr(ctx, varExpr);
    return varExpr;
}

antlrcpp::Any TypeChecker::visitUpperCaseIdentifier(BSVParser::UpperCaseIdentifierContext *ctx) {
    currentContext->logstream << "unhandled visitUpperCaseIdentifier: " << ctx->getText() << endl;
    assert(0);
    return freshConstant(__FUNCTION__, typeSort);
}

antlrcpp::Any TypeChecker::visitAnyidentifier(BSVParser::AnyidentifierContext *ctx) {
    currentContext->logstream << "unhandled visitAnyidentifier: " << ctx->getText() << endl;
    assert(0);
    return freshConstant(__FUNCTION__, typeSort);
}

antlrcpp::Any TypeChecker::visitExportdecl(BSVParser::ExportdeclContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitExportitem(BSVParser::ExportitemContext *ctx) {
    if (ctx->anyidentifier()) {
        string name = ctx->anyidentifier()->getText();
        shared_ptr<Declaration> valueDecl = currentContext->declaration[name];
        shared_ptr<Declaration> typeDecl = currentContext->typeDeclaration[name];
        if (valueDecl) {
            lexicalScope->bind(name, valueDecl);
        }
        if (typeDecl) {
            lexicalScope->bind(name, typeDecl);
        }
    } else if (ctx->packageide()) {
        string exportedPackageName = ctx->packageide()->getText();
        shared_ptr<LexicalScope> exportedPackage = packageScopes[exportedPackageName];
        lexicalScope->import(exportedPackage);
    }
    return nullptr;
}

antlrcpp::Any TypeChecker::visitImportdecl(BSVParser::ImportdeclContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitPackagestmt(BSVParser::PackagestmtContext *ctx) {
    setupZ3Context();
    currentContext->logstream << "visitPackagestmt at " << sourceLocation(ctx) << endl;
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitPackageide(BSVParser::PackageideContext *ctx) {
    assert(0);
    return freshConstant(__FUNCTION__, typeSort);
}

antlrcpp::Any TypeChecker::visitInterfacedecl(BSVParser::InterfacedeclContext *ctx) {
    // handled by addDeclaration now
    return freshConstant(__FUNCTION__, typeSort);
}

antlrcpp::Any TypeChecker::visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) {
    currentContext->logstream << "visitInterfacememberdecl: " << ctx->getText() << endl;
    if (ctx->methodproto())
        return visit(ctx->methodproto());
    else if (ctx->subinterfacedecl())
        return visit(ctx->subinterfacedecl());
    return nullptr;
}

antlrcpp::Any TypeChecker::visitMethodproto(BSVParser::MethodprotoContext *ctx) {
    shared_ptr<BSVType> methodType = bsvtype(ctx);
    currentContext->logstream << "Visit method proto " << ctx->getText();
    if (methodType) {
        currentContext->logstream << " : ";
        methodType->prettyPrint(currentContext->logstream);
    }
    currentContext->logstream << endl;
    return (Declaration *) new MethodDeclaration(currentContext->packageName, ctx->name->getText(), methodType, sourcePos(ctx));
}

antlrcpp::Any TypeChecker::visitMethodprotoformals(BSVParser::MethodprotoformalsContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitMethodprotoformal(BSVParser::MethodprotoformalContext *formal) {
    string formalName = formal->name->getText();
    lexicalScope->bind(formalName,
                       make_shared<Declaration>(string(), formalName, make_shared<BSVType>(), MethodParamBindingType));
    currentContext->logstream << "method proto formal " << formalName << endl;

    z3::expr formalExpr = context.constant(context.str_symbol(formalName.c_str()), typeSort);

    if (formal->bsvtype()) {
        shared_ptr<BSVType> formaltype = bsvtype(formal->bsvtype());
        currentContext->logstream << "method proto formal bsvtype: " << formaltype->to_string() << " at " << sourceLocation(formal) << endl;
        z3::expr typeExpr = bsvTypeToExpr(formaltype);
        addConstraint(formalExpr == typeExpr, "mpf$trk", formal);
        currentContext->logstream << "method proto formal constraint: " << (formalExpr == typeExpr) << endl;
    } else {
        currentContext->logstream << "visitMethodprotoFormal: fixme no type " << formalName << endl;
    }
    insertExpr(formal, formalExpr);
    return formalExpr;
}

antlrcpp::Any TypeChecker::visitSubinterfacedecl(BSVParser::SubinterfacedeclContext *ctx) {
    currentContext->logstream << "visit subinterfacedecl " << ctx->getText() << endl;
    string name(ctx->lowerCaseIdentifier()->getText());
    shared_ptr<BSVType> subinterfaceType(bsvtype(ctx->bsvtype()));
    Declaration *subinterfaceDecl = new InterfaceDeclaration(currentContext->packageName, name, subinterfaceType, sourcePos(ctx));
    return subinterfaceDecl;
}

antlrcpp::Any TypeChecker::visitTypedeftype(BSVParser::TypedeftypeContext *ctx) {
    assert(0);
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypeformals(BSVParser::TypeformalsContext *ctx) {
    assert(0);
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypeformal(BSVParser::TypeformalContext *ctx) {
    assert(0);
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypedefsynonym(BSVParser::TypedefsynonymContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitTypedefenum(BSVParser::TypedefenumContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitTypedefenumelement(BSVParser::TypedefenumelementContext *ctx) {
    BSVParser::UpperCaseIdentifierContext *tag = ctx->tag;
    string name(tag->getText());
    shared_ptr<BSVType> bsvtype(new BSVType(name));
    shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
    //declarationList.push_back(decl);
    currentContext->enumtag.insert(make_pair(name, parentDecl));
    return decl;
}

antlrcpp::Any TypeChecker::visitTypedefstruct(BSVParser::TypedefstructContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitTypedeftaggedunion(BSVParser::TypedeftaggedunionContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitStructmember(BSVParser::StructmemberContext *ctx) {
    string name(ctx->lowerCaseIdentifier()->getText());
    if (ctx->bsvtype()) {
        shared_ptr<BSVType> bbb(bsvtype(ctx->bsvtype()));
        return make_shared<Declaration>(name, bbb);
    } else if (ctx->subunion()) {
        assert(0);
    } else {
        assert(0);
    }    }

antlrcpp::Any TypeChecker::visitUnionmember(BSVParser::UnionmemberContext *ctx) {
    string name(ctx->upperCaseIdentifier()->getText());
    if (ctx->bsvtype()) {
        shared_ptr<BSVType> bbb(bsvtype(ctx->bsvtype()));
        return make_shared<Declaration>(name, bbb);
    } else if (ctx->subunion()) {
        assert(0);
    } else if (ctx->substruct()) {
        assert(0);
    } else {
        assert(0);
    }
}

antlrcpp::Any TypeChecker::visitSubstruct(BSVParser::SubstructContext *ctx) {
    assert(0);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitSubunion(BSVParser::SubunionContext *ctx) {
    assert(0);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitDerives(BSVParser::DerivesContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitVarbinding(BSVParser::VarbindingContext *ctx) {
    BindingType bindingType = lexicalScope->isGlobal() ? GlobalBindingType : LocalBindingType;
    if (lexicalScope->isGlobal()) {
        currentContext->logstream << " setupZ3Context should not be needed here" << endl;
        setupZ3Context();
        solver.push();
    }
    vector<BSVParser::VarinitContext *> varinits = ctx->varinit();
    for (size_t i = 0; i < varinits.size(); i++) {
        BSVParser::VarinitContext *varinit = varinits[i];

        z3::expr rhsexpr(context);
        if (varinit->rhs) {
            // visit RHS before adding the LHS binding in case the binding shadows a variable used in the RHS
            //FIXME: make this more robust
            rhsexpr = visit(varinit->rhs);
        }

        string varName = varinit->var->getText();
        shared_ptr<BSVType> varType = (ctx->t ? bsvtype(ctx->t) : make_shared<BSVType>());
        shared_ptr<Declaration> varDecl = (!lexicalScope->isGlobal()
                                           ? make_shared<Declaration>(currentContext->packageName, varName, varType, bindingType, sourcePos(ctx))
                                           : make_shared<FunctionDefinition>(string(), varName, varType, bindingType, sourcePos(ctx)));
        if (lexicalScope->isGlobal()) {
            currentContext->logstream << "visitVarBinding " << varName << " at " << sourceLocation(varinit) << endl;
        }
        lexicalScope->bind(varName, varDecl);

        z3::expr lhsexpr = visit(varinit->var);
        if (ctx->t) {
            z3::expr bsvtypeExpr = visit(ctx->t);
            addConstraint(lhsexpr == bsvtypeExpr, "varinit$lhs", varinit);
            currentContext->logstream << "visit VarInit lhs " << (lhsexpr == bsvtypeExpr) << " at " << sourceLocation(varinit) << endl;
        }
        if (varinit->rhs) {
            addConstraint(lhsexpr == rhsexpr, "varinit$rhs", varinit);
            currentContext->logstream << "visit VarInit rhs " << (lhsexpr == rhsexpr) << " at " << sourceLocation(varinit->rhs) << endl;
        } else {
            currentContext->logstream << "varinit with no rhs " << varinit->getText() << endl;
        }
    }
    if (lexicalScope->isGlobal()) {
        solver.pop();
    }
    return nullptr;
}

antlrcpp::Any TypeChecker::visitActionbinding(BSVParser::ActionbindingContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;
    currentContext->logstream << "        TypeChecker visiting action binding " << ctx->getText() << endl;

    string varname(ctx->var->getText().c_str());
    BindingType bindingType = lexicalScope->isGlobal() ? GlobalBindingType : LocalBindingType;
    assert(!lexicalScope->isGlobal());
    shared_ptr<Declaration> varDecl (make_shared<Declaration>(string(), varname, make_shared<BSVType>(), bindingType));
    lexicalScope->bind(varname, varDecl);
    z3::expr varsym = context.constant(context.str_symbol(varDecl->uniqueName.c_str()), typeSort);

    if (ctx->bsvtype()) {
        z3::expr interfaceType = visit(ctx->bsvtype());
        currentContext->logstream << "action binding constraint " << (interfaceType == varsym) << endl;
        addConstraint(interfaceType == varsym, "actionbindingt", ctx);
    }
    z3::expr rhstype = visit(ctx->rhs);
    z3::expr lhstype = instantiateType(actionContext ? "ActionValue" : "Module",
                                       varsym);
    addConstraint(lhstype == rhstype, "actionbinding", ctx);
    currentContext->logstream << "action binding rhs constraint " << (lhstype == rhstype) << endl;
    insertExpr(ctx, varsym);
    return varsym;
}

antlrcpp::Any TypeChecker::visitPatternbinding(BSVParser::PatternbindingContext *ctx) {
    currentContext->logstream << "Unimplemented pattern binding " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
    z3::expr patternExpr = visit(ctx->pattern());
    z3::expr rhsExpr = visit(ctx->expression());
    if (ctx->op->getText() == "<-") {
        addConstraint(instantiateType("ActionValue", patternExpr) == rhsExpr, "actionpatbinding$trk", ctx);
    } else {
        addConstraint(patternExpr == rhsExpr, "patbinding$trk", ctx);
    }
    return nullptr;
}

antlrcpp::Any TypeChecker::visitTypeclassdecl(BSVParser::TypeclassdeclContext *ctx) {
    currentContext->logstream << "visit type class decl " << ctx->typeclasside(0)->getText() << " at " << sourceLocation(ctx) << endl;
    return nullptr;
}

antlrcpp::Any TypeChecker::visitTypeclasside(BSVParser::TypeclassideContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypedepends(BSVParser::TypedependsContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypedepend(BSVParser::TypedependContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypelist(BSVParser::TypelistContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitOverloadeddecl(BSVParser::OverloadeddeclContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTctype(BSVParser::TctypeContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypeclassinstance(BSVParser::TypeclassinstanceContext *ctx) {
    currentContext->logstream << "visit typeclass instance at " << sourceLocation(ctx) << endl;
    return nullptr;
}

antlrcpp::Any TypeChecker::visitOverloadeddef(BSVParser::OverloadeddefContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitModuledef(BSVParser::ModuledefContext *ctx) {

    string module_name = ctx->moduleproto()->name->getText();
    shared_ptr<BSVType> moduleType(bsvtype(ctx->moduleproto()));
    currentContext->logstream << "tc ModuleDef " << module_name << " : ";
    moduleType->prettyPrint(currentContext->logstream);
    currentContext->logstream << endl;

    // declare the module in the global scope
    shared_ptr<ModuleDefinition> moduleDefinition = make_shared<ModuleDefinition>(currentContext->packageName, module_name, moduleType, sourcePos(ctx));
    currentContext->declaration[module_name] = moduleDefinition;
    currentContext->declarationList.push_back(moduleDefinition);
    lexicalScope->bind(module_name, moduleDefinition);

    // then setup the scope for the body of the module
    setupZ3Context();
    pushScope(module_name);
    solver.push();

    set<string> freeTypeVars = moduleType->freeVars();
    for (auto it = freeTypeVars.cbegin(); it != freeTypeVars.cend(); ++it) {
        string freevar = *it;
        z3::expr fvexpr = instantiateType("FreeVar", context.string_val(freevar));
        addConstraint(constant(freevar, typeSort) == fvexpr, "freevar$trk", ctx);
    }

    visit(ctx->moduleproto());

    //vector<BSVParser::ModulestmtContext *> stmts = ctx->modulestmt();
    for (int i = 0; ctx->modulestmt(i); i++) {
        currentContext->logstream << "module stmt " << ctx->modulestmt(i)->getText() << endl;
        visit(ctx->modulestmt(i));
    }
    z3::check_result checked = solver.check();
    currentContext->logstream << "  Type checking module " << module_name << ": " << check_result_name[checked] << endl;
    currentContext->logstream << solver << endl;
    if (checked == z3::sat) {
        z3::model mod = solver.get_model();
        currentContext->logstream << "model: " << mod << endl;
        currentContext->logstream << exprs.size() << " exprs" << endl;
        for (auto it = exprs.cbegin(); it != exprs.cend(); ++it) {
            z3::expr e = it->second;
            try {
                z3::expr v = mod.eval(e, true);
                currentContext->logstream << e << " evaluates to " << v << " for " << it->first->getText() << " at "
                                          << sourceLocation(it->first) << endl;
                exprTypes[it->first] = bsvtype(v, mod);
            } catch (const exception &e) {
                currentContext->logstream << "exception " << e.what() << " on expr: " << it->second << " @"
                                          << it->first->getRuleIndex()
                                          << " at " << sourceLocation(it->first) << endl;
            }
        }
    } else {
        z3::expr_vector unsat_core = solver.unsat_core();
        currentContext->logstream << "unsat_core " << unsat_core << endl;
        currentContext->logstream << "unsat_core.size " << unsat_core.size() << endl;
    }
    solver.pop();
    popScope();
    return moduleDefinition;
}

antlrcpp::Any TypeChecker::visitModuleproto(BSVParser::ModuleprotoContext *ctx) {
    if (ctx->moduleprotoformals())
        visit(ctx->moduleprotoformals());
    z3::expr_vector moduleInterfaceParams(context);
    moduleInterfaceParams.push_back(visit(ctx->moduleinterface));
    z3::expr moduleInterface = instantiateType("Module", moduleInterfaceParams);
    if (ctx->moduleprotoformals()) {
        z3::expr_vector formal_types(context);
        formal_types = visit(ctx->moduleprotoformals());
        formal_types.push_back(moduleInterface);
        string constructorName = "Function" + to_string(formal_types.size());
        z3::expr moduleProtoType = instantiateType(constructorName, formal_types);
        currentContext->logstream << "module proto type " << ctx->name->getText() << " z3::expr " << moduleProtoType << endl;
        return moduleProtoType;
    } else {
        return moduleInterface;
    }
}

antlrcpp::Any TypeChecker::visitModuleprotoformals(BSVParser::ModuleprotoformalsContext *ctx) {
    z3::expr_vector formal_types(context);
    for (int i = 0; i < ctx->children.size(); i++) {
        BSVParser::ModuleprotoformalContext *fp = ctx->moduleprotoformal(i);
        if (!fp)
            break;
        z3::expr formal_type = visit(fp);
        formal_types.push_back(formal_type);
    }
    return formal_types;
}

antlrcpp::Any TypeChecker::visitModuleprotoformal(BSVParser::ModuleprotoformalContext *formal) {
    string formalName = formal->name->getText();
    shared_ptr<Declaration> formalDecl = make_shared<Declaration>(string(), formalName, make_shared<BSVType>(), ModuleParamBindingType);
    lexicalScope->bind(formalName, formalDecl);

    z3::expr formalExpr = constant(formalDecl->uniqueName, typeSort);
    if (formal->bsvtype()) {
        z3::expr typeExpr = visit(formal->bsvtype());
        addConstraint(formalExpr == typeExpr, "mpf", formal);
        currentContext->logstream << "method proto formal constraint: " << (formalExpr == typeExpr) << endl;
    } else {
        currentContext->logstream << "visitMethodprotoFormal: fixme no type " << formal->name->getText() << endl;
    }
    insertExpr(formal, formalExpr);
    return formalExpr;
}

antlrcpp::Any TypeChecker::visitModulestmt(BSVParser::ModulestmtContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitModuleinst(BSVParser::ModuleinstContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitMethoddef(BSVParser::MethoddefContext *ctx) {
    string methodName(ctx->name->getText().c_str());
    currentContext->logstream << "    tc MethodDef " << methodName << " at " << sourceLocation(ctx) << endl;
    pushScope(methodName);
    actionContext = true;

    shared_ptr<BSVType> methodType = bsvtype(ctx);
    if (ctx->methodformals() != NULL) {
        visit(ctx->methodformals());
    }
    if (ctx->methodcond() != NULL) {
        z3::expr condtype = visit(ctx->methodcond());
    }
    vector<BSVParser::StmtContext *> stmts = ctx->stmt();
    for (int i = 0; i < stmts.size(); i++) {
        visit(stmts[i]);
        //FIXME: check return type
    }
    if (ctx->expression()) {
        z3::expr returnExpr = visit(ctx->expression());
        //FIXME: check return type
        //solver.add(returnExpr == returnType);
    }

    actionContext = false;
    popScope();
    return new MethodDefinition(ctx->name->getText(), methodType, sourcePos(ctx));
}

antlrcpp::Any TypeChecker::visitMethodformals(BSVParser::MethodformalsContext *ctx) {
    vector<BSVParser::MethodformalContext *> formals = ctx->methodformal();
    for (int i = 0; i < formals.size(); i++) {
        visit(formals[i]);
    }
    return 0;
}

antlrcpp::Any TypeChecker::visitMethodformal(BSVParser::MethodformalContext *formal) {
    string formalName = formal->lowerCaseIdentifier()->getText();
    shared_ptr<Declaration> formalDecl = make_shared<Declaration>(string(), formalName, make_shared<BSVType>(), MethodParamBindingType);
    lexicalScope->bind(formalName, formalDecl);
    currentContext->logstream << "method formal " << formalName << endl;

    z3::expr formalExpr = constant(formalDecl->uniqueName, typeSort);
    if (formal->bsvtype()) {
        z3::expr typeExpr = visit(formal->bsvtype());
        addConstraint(formalExpr == typeExpr, "methodformalt", formal);
        currentContext->logstream << "method formal constraint: " << (formalExpr == typeExpr) << endl;
    } else {
        currentContext->logstream << "visitMethodFormal: fixme no type " << formalName << endl;
    }
    insertExpr(formal, formalExpr);
    return formalExpr;
}

antlrcpp::Any TypeChecker::visitMethodcond(BSVParser::MethodcondContext *ctx) {
    z3::expr condtype = visit(ctx->expression());
    addConstraint(condtype == instantiateType("Bool"), "method$cond", ctx);
    return condtype;
}

antlrcpp::Any TypeChecker::visitSubinterfacedef(BSVParser::SubinterfacedefContext *ctx) {
    if (ctx->expression()) {
        //FIXME:
        visit(ctx->expression());
    } else {
        currentContext->logstream << "visitSubinterfacedef " << ctx->upperCaseIdentifier()->getText() << endl;
        vector<BSVParser::InterfacestmtContext *> stmts = ctx->interfacestmt();
        for (int i = 0; i < stmts.size(); i++) {
            visit(stmts[i]);
        }
    }
    return 0;
}

antlrcpp::Any TypeChecker::visitRuledef(BSVParser::RuledefContext *ctx) {
    currentContext->logstream << "    tc RuleDef " << ctx->name->getText() << endl;
    actionContext = true;

    if (ctx->rulecond() != NULL) {
        z3::expr condtype = visit(ctx->rulecond());
    }

    for (int i = 0; i < ctx->stmt().size(); i++) {
        visit(ctx->stmt().at(i));
    }

    actionContext = false;
    return freshConstant("rule", typeSort);
}

antlrcpp::Any TypeChecker::visitRulecond(BSVParser::RulecondContext *ctx) {
    z3::expr condtype = visit(ctx->expression());
    z3::func_decl boolcon = typeDecls.find("Bool")->second;
    addConstraint(condtype == boolcon(), "rulecond", ctx);
    insertExpr(ctx, condtype);
    return condtype;
}

antlrcpp::Any TypeChecker::visitFunctiondef(BSVParser::FunctiondefContext *ctx) {
    currentContext->logstream << "visit " << (lexicalScope->isGlobal() ? "global" : "local") << " function def" << endl;
    if (lexicalScope->isGlobal()) {
        setupZ3Context();
        solver.push();
    }
    bool wasActionContext = actionContext;
    string functionName = ctx->functionproto()->name->getText();
    string packageName = lexicalScope->isGlobal() ? currentContext->packageName : string();
    lexicalScope->bind(functionName,
                       make_shared<FunctionDefinition>(packageName, functionName, bsvtype(ctx->functionproto()),
                                                       LocalBindingType, sourcePos(ctx)));

    pushScope(functionName);
    actionContext = true;

    if (ctx->functionproto()->methodformals())
        visit(ctx->functionproto()->methodformals());

    for (int i = 0; ctx->stmt(i); i++) {
        visit(ctx->stmt(i));
    }

    popScope();

    actionContext = wasActionContext;
    if (lexicalScope->isGlobal()) {
        solver.pop();
    }
    return nullptr;
}

antlrcpp::Any TypeChecker::visitFunctionproto(BSVParser::FunctionprotoContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitExterncimport(BSVParser::ExterncimportContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitExterncfuncargs(BSVParser::ExterncfuncargsContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitExterncfuncarg(BSVParser::ExterncfuncargContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitVarassign(BSVParser::VarassignContext *ctx) {
    currentContext->logstream << "var assign " << ctx->getText() << endl;
    z3::expr lhsExpr = visit(ctx->lvalue(0));
    z3::expr rhsExpr = visit(ctx->expression());
    if (ctx->op->getText() == "<-") {
        string constructor = (actionContext ? "ActionValue" : "Module");
        currentContext->logstream << "var assign <- " << constructor << " " << lhsExpr << endl;
        lhsExpr = instantiateType(constructor, lhsExpr);
    }
    addConstraint(lhsExpr == rhsExpr, "varassign", ctx);
    return visitChildren(ctx);
}

z3::expr TypeChecker::visitArraysubLvalue(BSVParser::LvalueContext *ctx, BSVParser::ExprprimaryContext *array, BSVParser::ExpressionContext *index) {
    currentContext->logstream << "Visit array index lvalue at " << sourceLocation(ctx) << endl;

    z3::expr arrayExpr = visit(array);
    z3::expr indexExpr = visit(index);
    z3::expr typeexpr = freshConstant("arraysub$lvalue", typeSort);
    vector<z3::expr> exprs;
    exprs.push_back(typeexpr == instantiateType("Bit", instantiateType("Numeric", context.int_val(1))));
    exprs.push_back(arrayExpr == instantiateType("Vector",
                                                 instantiateType("Numeric", freshConstant("alindex", intSort)),
                                                 typeexpr));
    exprs.push_back(arrayExpr == instantiateType("Vector",
                                                 instantiateType("Numeric", freshConstant("alindex", intSort)),
                                                 instantiateType("Reg", typeexpr)));
    if (exprs.size())
        addConstraint(orExprs(exprs), "arraysub$lvalue", ctx);

    insertExpr(ctx, typeexpr);
    return typeexpr;
}


z3::expr TypeChecker::visitBitselLvalue(BSVParser::ExprprimaryContext *ctx,
                                        BSVParser::ExpressionContext *lsb,
                                        antlr4::Token *widthdown,
                                        antlr4::Token *widthup) {
    currentContext->logstream << "Visit bit selection lvalue at " << sourceLocation(ctx) << endl;

    z3::expr arrayExpr = visit(ctx);

    z3::expr typeexpr = freshConstant("bitsel$lvalue", typeSort);
    z3::expr bitwidthexpr = context.int_val(1);
    if (lsb) {
        // FIXME: add constraint we're expecting Bit Int UInt Integer
        bitwidthexpr = freshConstant("bitsel$width", intSort);
    } else if (widthdown) {
        bitwidthexpr = context.int_val((int) strtol(widthdown->getText().c_str(), 0, 0));
    } else if (widthup) {
        bitwidthexpr = context.int_val((int) strtol(widthup->getText().c_str(), 0, 0));
    }

    vector<z3::expr> exprs;
    exprs.push_back(typeexpr == instantiateType("Bit", instantiateType("Numeric", bitwidthexpr)));

    if (exprs.size())
        addConstraint(orExprs(exprs), "arraysub$lvalue", ctx);

    insertExpr(ctx, typeexpr);
    return typeexpr;
}

z3::expr TypeChecker::visitLFieldValue(BSVParser::LvalueContext *ctx, BSVParser::ExprprimaryContext *objctx, string fieldname) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    currentContext->logstream << "Visit field lvalue " << fieldname << endl;
    z3::expr objexpr = visit(objctx);
    z3::expr sym = freshConstant(fieldname, typeSort);
    vector<z3::expr> exprs;
    for (auto it = currentContext->memberDeclaration.find(fieldname);
         it != currentContext->memberDeclaration.end() && it->first == fieldname; ++it) {
        shared_ptr<Declaration> memberDecl(it->second);
        shared_ptr<Declaration> parentDecl(memberDecl->parent);
        shared_ptr<StructDeclaration> structDecl = parentDecl->structDeclaration();
        currentContext->logstream << "    field " << fieldname << " belongs to type " << parentDecl->name << endl;
        //FIXME continue here
        map<string, shared_ptr<BSVType>> mapping;
        shared_ptr<BSVType> freshParentType = freshType(parentDecl->bsvtype, mapping);
        z3::expr fieldexpr = bsvTypeToExpr(freshType(memberDecl->bsvtype, mapping));
        z3::expr fieldConstraint = (objexpr == bsvTypeToExpr(freshParentType) && sym == fieldexpr);
        currentContext->logstream << "    fieldConstraint " << fieldConstraint << endl;
        exprs.push_back(fieldConstraint);
    }
    if (exprs.size())
        addConstraint(orExprs(exprs), "fieldval", ctx);

    z3::expr fieldexpr = constant(fieldname, typeSort);
    insertExpr(ctx, fieldexpr);
    return fieldexpr;
}

antlrcpp::Any TypeChecker::visitLvalue(BSVParser::LvalueContext *ctx) {
    if (BSVParser::ExprprimaryContext *lhs = ctx->exprprimary()) {
        z3::expr lhsExpr = visit(lhs);
        if (ctx->msb != NULL) {
            currentContext->logstream << "bitsel lvalue with msb, widthdown or widthup at " << sourceLocation((ctx)) << endl;
            return visitBitselLvalue(lhs, ctx->msb, ctx->widthdown, ctx->widthup);
        } else if (ctx->index != NULL) {
            // lvalue [ index ]
            currentContext->logstream << "arraysub lvalue with index at " << sourceLocation((ctx)) << endl;
            return visitArraysubLvalue(ctx, lhs, ctx->index);
        } else if (ctx->lowerCaseIdentifier()) {
            // lvalue . field
            string fieldname = ctx->lowerCaseIdentifier()->getText();
            currentContext->logstream << "field lvalue <" << fieldname << "> at " << sourceLocation((ctx)) << endl;
            return visitLFieldValue(ctx, lhs, fieldname);
        } else {
            // should never occur
            assert(0);
        }
    } else {
        BSVParser::LowerCaseIdentifierContext *id = ctx->lowerCaseIdentifier();
        string varName = id->getText();
        shared_ptr<Declaration> varDecl = lookup(varName);
        if (!varDecl) {
            currentContext->logstream << "lvalue " << varName << " no decl at " << sourceLocation(id) << endl;
        }
        z3::expr varExpr = constant(varDecl->uniqueName, typeSort);
        return varExpr;
    }
    currentContext->logstream << "Unhandled lvalue " << ctx->getText() << endl;
    assert(0);
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitBsvtype(BSVParser::BsvtypeContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    shared_ptr<BSVType> bbb(bsvtype(ctx));
    currentContext->logstream << "typechecker::visitBsvtype " << ctx->getText() << " bbb ";
    bbb->prettyPrint(currentContext->logstream);
    currentContext->logstream << endl;
    shared_ptr<BSVType> derefType = dereferenceType(bbb);
    currentContext->logstream << "    deref type ";
    derefType->prettyPrint(currentContext->logstream);
    currentContext->logstream << endl;
    z3::expr bsvtype_expr = bsvTypeToExpr(derefType);

    insertExpr(ctx, bsvtype_expr);
    return bsvtype_expr;
}

antlrcpp::Any TypeChecker::visitTypeide(BSVParser::TypeideContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTypenat(BSVParser::TypenatContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitOperatorexpr(BSVParser::OperatorexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr bsvtype_expr = visit(ctx->binopexpr());

    insertExpr(ctx, bsvtype_expr);
    return bsvtype_expr;
}

antlrcpp::Any TypeChecker::visitCaseexpr(BSVParser::CaseexprContext *ctx) {
    currentContext->logstream << "visit case expr " << ctx->getText() << endl;
    z3::expr casetype = freshConstant("case", typeSort);
    z3::expr exprtype = visit(ctx->expression());
    size_t numitems = ctx->caseexprpatitem().size();
    for (size_t i = 0; i < numitems; i++) {
        BSVParser::CaseexprpatitemContext *item = ctx->caseexprpatitem(i);
        currentContext->logstream << "item = " << item << endl;
        if (item->body != NULL) {
            currentContext->logstream << "caseexpritem has pattern "
                                      << item->pattern()->getText()
                                      << " body " << item->body->getText()
                                      << endl;

            if (item->pattern() != NULL) {
                z3::expr itemtype = visit(item->pattern());
                addConstraint(exprtype == itemtype, "caseitem", item);
            }
            z3::expr bodytype = visit(item->body);
            addConstraint(casetype == bodytype, "casebody", item->body);
        }
    }
    for (size_t i = 0; ctx->caseexpritem(i); i++) {
        BSVParser::CaseexpritemContext *item = ctx->caseexpritem(i);
        currentContext->logstream << "caseexpritem has expression " << item->match->getText() << endl;

    }
    return casetype;
}

antlrcpp::Any TypeChecker::visitMatchesexpr(BSVParser::MatchesexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr expr = visit(ctx->expression());
    z3::expr patternExpr = visit(ctx->pattern());
    addConstraint(expr == patternExpr, "matches$expr", ctx);
    for (int i = 0; ctx->patterncond(i); i++) {
        visit(ctx->patterncond(i));
    }

    z3::expr boolExpr = instantiateType("Bool");
    insertExpr(ctx, boolExpr);

    return boolExpr;
}

antlrcpp::Any TypeChecker::visitCondexpr(BSVParser::CondexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr boolExpr = visit(ctx->expression(0));
    z3::expr thenExpr = visit(ctx->expression(1));
    z3::expr elseExpr = visit(ctx->expression(2));
    addConstraint(boolExpr == instantiateType("Bool"), "boolexpr$trk", ctx->expression(0));
    addConstraint(thenExpr == elseExpr, "condexpr$trk", ctx);

    insertExpr(ctx, thenExpr);
    return thenExpr;
}

antlrcpp::Any TypeChecker::visitCaseexpritem(BSVParser::CaseexpritemContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitPatterncond(BSVParser::PatterncondContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr expr = visit(ctx->expression());
    z3::expr boolExpr = instantiateType("Bool");
    addConstraint(expr == boolExpr, "patterncond$trk", ctx);

    insertExpr(ctx, boolExpr);
    return boolExpr;
}

antlrcpp::Any TypeChecker::visitBinopexpr(BSVParser::BinopexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    if (ctx->unopexpr() != NULL) {
        z3::expr bsvtype_expr = visit(ctx->unopexpr());
        insertExpr(ctx, bsvtype_expr);
        return bsvtype_expr;
    }

    currentContext->logstream << "        Visit binop " << ctx->getText() << endl;

    z3::expr leftsym = visit(ctx->left);
    z3::expr rightsym = visit(ctx->right);

    addConstraint(leftsym == rightsym, "binop$args", ctx);
    if (0) {
        solver.push();
        currentContext->logstream << "  checking " << ctx->getText() << endl;
        //currentContext->logstream << solver << endl;
        currentContext->logstream << "        check(" << ctx->getText() << ") " << check_result_name[solver.check()]
                                  << endl;
        solver.pop();
    }

    string opstr(ctx->op->getText());
    string binopstr(freshString(opstr));
    z3::expr binopsym = constant(binopstr, typeSort);

    currentContext->logstream << "Arith expr " << ctx->getText() << endl;
    vector<z3::expr> exprs;
    if (opstr == "||" || opstr == "&&") {
        exprs.push_back(leftsym == instantiateType("Bool"));
    } else if (opstr != "==" && opstr != "!=") {
        z3::expr exprszsym = instantiateType("Numeric", freshConstant("binop$sz", intSort));
        exprs.push_back(leftsym == instantiateType("Bit", exprszsym));
        exprs.push_back(leftsym == instantiateType("Int", exprszsym));
        exprs.push_back(leftsym == instantiateType("UInt", exprszsym));
        exprs.push_back(leftsym == instantiateType("Integer"));
        exprs.push_back(leftsym == instantiateType("Real"));
        exprs.push_back(leftsym == instantiateType("String"));
    }
    if (exprs.size()) {
        z3::expr binopExpr = orExprs(exprs);
        addConstraint(binopExpr, "binop$type", ctx);
    }
    
    if (boolops.find(opstr) != boolops.end()) {
        currentContext->logstream << "Bool expr " << ctx->getText() << endl;
        addConstraint(binopsym == instantiateType("Bool"), "binboolop$res", ctx);
    } else {
        addConstraint(binopsym == leftsym, "binop$res", ctx);
    }

    insertExpr(ctx, binopsym);
    return binopsym;
}

antlrcpp::Any TypeChecker::visitUnopexpr(BSVParser::UnopexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    BSVParser::ExprprimaryContext *ep = ctx->exprprimary();
    currentContext->logstream << " visiting unop " << ctx->getText() << " " << endl;

    z3::expr unopExpr = visit(ep);
    currentContext->logstream << " visit unop " << ctx->getText() << " " << unopExpr << " at " <<  sourceLocation(ctx) << endl;
    if (ctx->op == NULL) {
        insertExpr(ctx, unopExpr);
        return unopExpr;
    }

    string op = ctx->op->getText();
    if (op == "!") {
        z3::expr boolExpr = instantiateType("Bool");
        addConstraint(unopExpr == boolExpr, "unop", ctx);
        insertExpr(ctx, boolExpr);
        return boolExpr;
    } else if (op == "&" || op == "~&"
               || op == "|" || op == "~|"
                || op == "^" || op == "^~" || op == "^~") {
        addConstraint(unopExpr == instantiateType("Bit", instantiateType("Numeric", freshConstant("bit$width", intSort))),
                "bit$reduce", ctx);
        z3::expr bit1Expr = instantiateType("Bit", instantiateType("Numeric", context.int_val(1)));
        insertExpr(ctx, bit1Expr);
        return bit1Expr;
    } else {
        insertExpr(ctx, unopExpr);
        return unopExpr;
    }
}

antlrcpp::Any TypeChecker::visitBitconcat(BSVParser::BitconcatContext *ctx) {
    z3::expr bitwidth = freshConstant("bitconcat", intSort);
    for (int i = 0; ctx->expression(i); i++) {
        BSVParser::ExpressionContext *expr = ctx->expression(i);
        z3::expr z3expr = visit(expr);
        z3::expr exprwidth = freshConstant("bitexprwidth", intSort);
        z3::expr bitexpr = instantiateType("Bit", instantiateType("Numeric", exprwidth));
        addConstraint(bitexpr == z3expr, "trkbitconcat", ctx);
    }
    //FIXME: add up the exprwidths
    return instantiateType("Bit", instantiateType("Numeric", bitwidth));
}

antlrcpp::Any TypeChecker::visitVarexpr(BSVParser::VarexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;
    currentContext->logstream << "Visiting var expr " << ctx->getText().c_str() << " " << ctx << endl;

    string varname(ctx->lowerCaseIdentifier()->getText());
    string packageName;
    if (ctx->upperCaseIdentifier(0)) {
        packageName = ctx->upperCaseIdentifier(0)->getText();
        cerr << "package specifier for " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
    }
    shared_ptr<Declaration> varDecl = ctx->upperCaseIdentifier(0) ? lookup(varname, ctx->upperCaseIdentifier(0)->getText()) : lookup(varname);
    varDecls[ctx] = varDecl;
    if (varDecl) {
        currentContext->logstream << "    uniqname " << varDecl->uniqueName << " bindingType " << varDecl->bindingType << endl;
    } else {
        currentContext->logstream << "    no decl found at " << sourceLocation(ctx) << endl;
    }
    assert(varDecl);
    if (!varDecl || varDecl->bindingType == GlobalBindingType) {
        currentContext->logstream << "visiting global var " << varname << " at " << sourceLocation(ctx) << endl;
        if (varDecl && varDecl->bsvtype) {
            varDecl->bsvtype->prettyPrint(currentContext->logstream);
            currentContext->logstream << endl;
            shared_ptr<BSVType> derefType = dereferenceType(varDecl->bsvtype);
            if (varDecl->functionDefinition() || varDecl->moduleDefinition()) {
                derefType = freshType(derefType);
                currentContext->logstream << "global " << varname << " freshType " << derefType->to_string() << endl;
            }
            z3::expr varExpr = bsvTypeToExpr(derefType);
            insertExpr(ctx, varExpr);
            return varExpr;
        }
    }

    string uniqueName = (varDecl) ? varDecl->uniqueName : varname;
    string rhsname(uniqueName + string("-rhs"));
    z3::expr varExpr = constant(uniqueName, typeSort);
    z3::expr rhsExpr = constant(rhsname, typeSort);


    if (currentContext->enumtag.find(varname) != currentContext->enumtag.end()) {
        z3::expr var = context.constant(context.str_symbol(varname.c_str()), typeSort);
        vector<z3::expr> exprs;
        for (auto it = currentContext->enumtag.find(varname); it != currentContext->enumtag.end() && it->first == varname; ++it) {
            shared_ptr<Declaration> decl(it->second);
            currentContext->logstream << "Tag " << varname << " of type " << decl->name << endl;
            z3::func_decl type_decl = typeDecls.find(decl->name)->second;
            exprs.push_back(rhsExpr == type_decl());
        }

        addConstraint(orExprs(exprs), "enumtag", ctx);
    } else if (!varDecl || varDecl->bindingType == GlobalBindingType) {
        //addConstraint(varExpr == rhsExpr, "varexpr", ctx);
        rhsExpr = varExpr;
    } else {
        // variable
        z3::expr regExpr = instantiateType("Reg", rhsExpr);
        addConstraint(varExpr == regExpr || varExpr == rhsExpr, "varexpr", ctx);
    }
    insertExpr(ctx, rhsExpr);
    currentContext->logstream << "visit var expr " << ctx->getText() << " rhs expr " << rhsExpr << " ctx " << ctx << endl;
    return rhsExpr;
}

antlrcpp::Any TypeChecker::visitBlockexpr(BSVParser::BlockexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr blockExpr = freshConstant("blockexpr", typeSort);
    pushScope("blockexpr");
    visitChildren(ctx);
    popScope();

    insertExpr(ctx, blockExpr);
    return blockExpr;
}

antlrcpp::Any TypeChecker::visitStringliteral(BSVParser::StringliteralContext *ctx) {
    z3::expr expr = instantiateType("String");
    insertExpr(ctx, expr);
    return expr;
}

antlrcpp::Any TypeChecker::visitIntliteral(BSVParser::IntliteralContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;
    currentContext->logstream << "        Visiting int literal "<< ctx->getText() << endl;
    z3::expr sym = context.constant(freshName("intlit"), typeSort);
    z3::expr widthExpr = context.constant(freshName("ilitsz"), intSort);

    addConstraint((sym == typeDecls.at("Integer")())
                  || (sym == instantiateType("Bit", instantiateType("Numeric", widthExpr))),
                  "intlit",
                  ctx);

    if (0) {
        solver.push();
        currentContext->logstream << "        check() " << check_result_name[solver.check()] << endl;
        solver.pop();
    }

    insertExpr(ctx, sym);
    return sym;
}

antlrcpp::Any TypeChecker::visitRealliteral(BSVParser::RealliteralContext *ctx) {
    z3::expr expr = instantiateType("Real");
    insertExpr(ctx, expr);
    return expr;
}

antlrcpp::Any TypeChecker::visitCastexpr(BSVParser::CastexprContext *ctx) {
    shared_ptr<BSVType> type = bsvtype(ctx->bsvtype());
    z3::expr typeExpr = bsvTypeToExpr(type);
    z3::expr expr = visit(ctx->exprprimary());
    //addConstraint(typeExpr == expr, "typeassertion$trk", ctx);
    currentContext->logstream << "cast expr " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
    insertExpr(ctx, typeExpr);
    return typeExpr;
}

antlrcpp::Any TypeChecker::visitTypeassertionexpr(BSVParser::TypeassertionexprContext *ctx) {
    shared_ptr<BSVType> type = bsvtype(ctx->bsvtype());
    z3::expr typeExpr = bsvTypeToExpr(type);
    z3::expr expr = visit(ctx->expression(0));
    assert(ctx->expression(1) == nullptr);
    addConstraint(typeExpr == expr, "typeassertion$trk", ctx);
    insertExpr(ctx, typeExpr);
    return typeExpr;
}

antlrcpp::Any TypeChecker::visitResetbyexpr(BSVParser::ResetbyexprContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitUndefinedexpr(BSVParser::UndefinedexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;
    z3::expr undefined = freshConstant("_undefined_", typeSort);
    insertExpr(ctx, undefined);
    return undefined;
}

antlrcpp::Any TypeChecker::visitClockedbyexpr(BSVParser::ClockedbyexprContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}


antlrcpp::Any TypeChecker::visitActionvalueblockexpr(BSVParser::ActionvalueblockexprContext *ctx) {
    z3::expr expr = visit(ctx->actionvalueblock());
    insertExpr(ctx, expr);
    return expr;
}

antlrcpp::Any TypeChecker::visitFieldexpr(BSVParser::FieldexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr exprtype = visit(ctx->exprprimary());
    string fieldname = ctx->field->getText();

    currentContext->logstream << "Visit field expr " << fieldname << " exprtype " << exprtype << endl;

    z3::expr sym = context.constant(context.str_symbol(fieldname.c_str()), typeSort);

    vector<z3::expr> exprs;
    z3::expr fieldexpr = freshConstant(fieldname, typeSort);

    for (auto it = currentContext->memberDeclaration.find(fieldname);
         it != currentContext->memberDeclaration.end() && it->first == fieldname; ++it) {
        shared_ptr<Declaration> memberDecl(it->second);
        shared_ptr<Declaration> parentDecl(memberDecl->parent);
        currentContext->logstream << "    field " << fieldname << " member decl " << memberDecl->name;
        if (parentDecl) {
            currentContext->logstream << " belongs to type " << parentDecl->name << endl;
        } else {
            currentContext->logstream << " missing parentDecl" << endl;
            assert(0);
        }
        z3::expr type_expr = bsvTypeToExpr(freshType(parentDecl->bsvtype));

        shared_ptr<StructDeclaration> structDecl = parentDecl->structDeclaration();
        shared_ptr<InterfaceDeclaration> interfaceDecl = parentDecl->interfaceDeclaration();
        if (interfaceDecl) {
            currentContext->logstream << " interface decl " << interfaceDecl->name << endl;

            shared_ptr<MethodDeclaration> methodDecl = memberDecl->methodDeclaration();
            shared_ptr<InterfaceDeclaration> subinterfaceDecl = memberDecl->interfaceDeclaration();
            if (methodDecl)
                currentContext->logstream << " method decl " << methodDecl->name << endl;
            if (subinterfaceDecl)
                currentContext->logstream << " subinterface decl " << subinterfaceDecl->name << endl;
            if (methodDecl) {
                shared_ptr<BSVType> interfaceType = dereferenceType(interfaceDecl->bsvtype);
                shared_ptr<BSVType> methodType = dereferenceType(methodDecl->bsvtype);
                currentContext->logstream << "interface method ";
                interfaceType->prettyPrint(currentContext->logstream);
                currentContext->logstream << " method ";
                methodType->prettyPrint(currentContext->logstream);
                currentContext->logstream << endl;
                map<string, shared_ptr<BSVType>> freshTypeVars;
                z3::expr interfaceExpr = bsvTypeToExpr(freshType(interfaceType, freshTypeVars));
                z3::expr methodExpr = bsvTypeToExpr(freshType(methodType, freshTypeVars));
                currentContext->logstream << "convert method " << fieldname << " args to z3::expr "
                                          << sourceLocation(ctx) << endl;
                currentContext->logstream << "    " << interfaceExpr << endl;
                currentContext->logstream << "    " << methodExpr << endl;
                currentContext->logstream << "    " << (exprtype == interfaceExpr && fieldexpr == methodExpr)
                                          << endl;
                exprs.push_back(exprtype == interfaceExpr && fieldexpr == methodExpr);
            } else if (subinterfaceDecl) {
                shared_ptr<BSVType> interfaceType = dereferenceType(interfaceDecl->bsvtype);
                shared_ptr<BSVType> subinterfaceType = dereferenceType(subinterfaceDecl->bsvtype);
                currentContext->logstream << "interface type ";
                interfaceType->prettyPrint(currentContext->logstream);
                currentContext->logstream << " subinterface type ";
                subinterfaceType->prettyPrint(currentContext->logstream);
                currentContext->logstream << endl;
                map<string, shared_ptr<BSVType>> freshTypeVars;
                z3::expr interfaceExpr = bsvTypeToExpr(freshType(interfaceType, freshTypeVars));
                z3::expr subinterfaceExpr = bsvTypeToExpr(freshType(subinterfaceType, freshTypeVars));
                currentContext->logstream << "convert subinterface " << fieldname << " args to z3::expr "
                                          << sourceLocation(ctx) << endl;
                currentContext->logstream << "    " << interfaceExpr << endl;
                currentContext->logstream << "    " << subinterfaceExpr << endl;
                currentContext->logstream << "    " << (exprtype == interfaceExpr && fieldexpr == subinterfaceExpr)
                                          << endl;
                exprs.push_back(exprtype == interfaceExpr && fieldexpr == subinterfaceExpr);
            } else {
                assert(0);
            }
        } else if (structDecl) {
            currentContext->logstream << " struct decl " << structDecl->name << endl;
            shared_ptr<Declaration> fieldDecl = memberDecl;
            shared_ptr<BSVType> structType = dereferenceType(structDecl->bsvtype);
            shared_ptr<BSVType> fieldType = dereferenceType(fieldDecl->bsvtype);
            currentContext->logstream << "struct type ";
            structType->prettyPrint(currentContext->logstream);
            currentContext->logstream << " field <" << fieldDecl->name << "> type ";
            fieldType->prettyPrint(currentContext->logstream);
            currentContext->logstream << endl;
            map<string, shared_ptr<BSVType>> freshTypeVars;
            z3::expr structExpr = bsvTypeToExpr(freshType(structType, freshTypeVars));
            z3::expr memberExpr = bsvTypeToExpr(freshType(fieldType, freshTypeVars));
            currentContext->logstream << "convert field args to z3::expr " << sourceLocation(ctx) << endl;
            currentContext->logstream << "    " << structExpr << endl;
            currentContext->logstream << "    " << memberExpr << endl;
            currentContext->logstream << "    " << (exprtype == structExpr && fieldexpr == memberExpr)
                                      << endl;
            exprs.push_back(exprtype == structExpr && fieldexpr == memberExpr);
        } else {
            exprs.push_back(sym == type_expr);
        }
    }
    //z3::expr tracker(freshConstant("$track", boolSort));
    //insertTracker(ctx, tracker);
    if (exprs.size()) {
        z3::expr orExpr = orExprs(exprs);
        addConstraint(orExpr, "fieldexpr", ctx);
        currentContext->logstream << " returning fieldexpr " << fieldname << " exprs " << orExpr << endl;
    }

    insertExpr(ctx, fieldexpr);
    return fieldexpr;
}

antlrcpp::Any TypeChecker::visitParenexpr(BSVParser::ParenexprContext *ctx) {
    z3::expr parenExpr = visit(ctx->expression());
    insertExpr(ctx, parenExpr);
    return parenExpr;
}

shared_ptr<BSVType> TypeChecker::resolveInterfaceTag(shared_ptr<BSVType> interfaceTypeOrTag) {
    auto it = currentContext->typeDeclaration.find(interfaceTypeOrTag->name);
    if (it == currentContext->typeDeclaration.cend())
        return interfaceTypeOrTag;
    shared_ptr<Declaration> typeDeclaration = it->second;
    if (typeDeclaration->bsvtype->params.size() == interfaceTypeOrTag->params.size())
        return interfaceTypeOrTag;
    vector<shared_ptr<BSVType>> params;
    for (int i = 0; i < typeDeclaration->bsvtype->params.size(); i++)
        params.push_back(make_shared<BSVType>());
    //FIXME: numeric
    return make_shared<BSVType>(interfaceTypeOrTag->name, params);
}

antlrcpp::Any TypeChecker::visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) {
    shared_ptr<BSVType> interfaceTypeOrTag(bsvtype(ctx->bsvtype()));
    shared_ptr<BSVType> interfaceType = dereferenceType(resolveInterfaceTag(interfaceTypeOrTag));
    z3::expr interfaceExpr = bsvTypeToExpr(interfaceType);
    for (int i = 0; ctx->interfacestmt(i); i++) {
        visit(ctx->interfacestmt(i));
    }
    insertExpr(ctx, interfaceExpr);
    return interfaceExpr;
}

antlrcpp::Any TypeChecker::visitCallexpr(BSVParser::CallexprContext *ctx) {
    vector<BSVParser::ExpressionContext *> args = ctx->expression();
    currentContext->logstream << "visit call expr " << ctx->getText() << (actionContext ? " side effect " : " constructor ") << " arity " << args.size() << endl;
    z3::expr instance_expr = freshConstant((actionContext ? "call$trk" : "mkinstance"), typeSort);
    z3::expr fcn_expr = visit(ctx->fcn);

    if (args.size() == 0) {
        // special case, not a Function#() type, just the return type
        addConstraint(instance_expr == fcn_expr, ctx->fcn->getText(), ctx);
        return instance_expr;
    }

    z3::expr_vector arg_exprs(context);
    for (int i = 0; i < args.size(); i++) {
        //FIXME check parameters
        z3::expr arg_expr = visit(args[i]);
        arg_exprs.push_back(arg_expr);
    }
    string constructorName = "Function" + to_string(args.size() + 1);
    arg_exprs.push_back(instance_expr);
    currentContext->logstream << "instantiate " << constructorName << " arity " << arg_exprs.size() << endl;
    z3::expr result_expr = instantiateType(constructorName, arg_exprs);
    currentContext->logstream << "   constraint " << (result_expr == fcn_expr) << endl;
    addConstraint(result_expr == fcn_expr, ctx->fcn->getText(), ctx);
    insertExpr(ctx, instance_expr);
    return instance_expr;
}

antlrcpp::Any TypeChecker::visitSyscallexpr(BSVParser::SyscallexprContext *ctx) {
    currentContext->logstream << "visit syscall at " << sourceLocation(ctx) << endl;
    currentContext->logstream << "      syscall   " << ctx->getText() << endl;
    visitChildren(ctx);
    z3::expr expr = freshConstant("syscall", typeSort);
    insertExpr(ctx, expr);
    return expr;
}

antlrcpp::Any TypeChecker::visitValueofexpr(BSVParser::ValueofexprContext *ctx) {
    visit(ctx->bsvtype());
    z3::expr expr = instantiateType("Integer");
    insertExpr(ctx, expr);
    return expr;
}

antlrcpp::Any TypeChecker::visitTaggedunionexpr(BSVParser::TaggedunionexprContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    string tagname = ctx->tag->getText();
    currentContext->logstream << "tagged expr " << tagname << " at " << sourceLocation(ctx) << endl;
    string exprname(freshString(tagname));
    z3::expr exprsym = constant(exprname, typeSort);

    if (ctx->exprprimary()) {
        z3::expr expr = visit(ctx->exprprimary());
    } else {
        BSVParser::MemberbindsContext *memberbinds = ctx->memberbinds();
        if (memberbinds) {
            for (int i = 0; memberbinds->memberbind(i); ++i) {
                BSVParser::MemberbindContext *mb = memberbinds->memberbind(i);
                visit(mb);
            }
        }
    }

    vector<z3::expr> exprs;
    for (auto it = currentContext->enumtag.find(tagname); it != currentContext->enumtag.end() && it->first == tagname; ++it) {
        shared_ptr<Declaration> decl(it->second);
        shared_ptr<BSVType> freshTypeInstance = freshType(decl->bsvtype);
        z3::expr tagConstraint = (exprsym == bsvTypeToExpr(freshTypeInstance));
        currentContext->logstream << "Tag exprprimary " << tagname << " of type " << freshTypeInstance->to_string() << endl;
        currentContext->logstream << " tag constraint " << tagConstraint << " at " << sourceLocation(ctx) << endl;
        exprs.push_back(tagConstraint);
    }
    auto tt = currentContext->typeDeclaration.find(tagname);
    if (tt != currentContext->typeDeclaration.cend()) {
        shared_ptr<Declaration> tagDecl = tt->second;
        currentContext->logstream << "  tag decl " << tagDecl->name << " declType " << endl;
        shared_ptr<StructDeclaration> structDecl = tagDecl->structDeclaration();
        if (structDecl) {
            shared_ptr<BSVType> freshTypeInstance = freshType(structDecl->bsvtype);
            z3::expr structConstraint = exprsym == bsvTypeToExpr(freshTypeInstance);
            currentContext->logstream << "  struct constraint " << structConstraint << " at " << sourceLocation(ctx) << endl;
            exprs.push_back(structConstraint);
        }
    }
    if (exprs.size())
        addConstraint(orExprs(exprs), tagname + "$trk", ctx);
    else
        currentContext->logstream << "No enum definitions for expr " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
    solver.push();
    checkSolution(ctx);
    solver.pop();
    insertExpr(ctx, exprsym);
    return exprsym;
}

antlrcpp::Any TypeChecker::visitArraysub(BSVParser::ArraysubContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr arrayExpr = visit(ctx->array);
    z3::expr msbExpr = visit(ctx->msb);
    z3::expr bitSelWidth = context.int_val(1);
    if (ctx->widthdown) {
        currentContext->logstream << "visit arraysub bit slice down " << ctx->getText() << " at " << sourceLocation(ctx) << endl;

        bitSelWidth = context.int_val((int) strtol(ctx->widthdown->getText().c_str(), 0, 0));
    } else if (ctx->widthup) {

        currentContext->logstream << "visit arraysub bit slice up " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
        bitSelWidth = context.int_val((int) strtol(ctx->widthup->getText().c_str(), 0, 0));
    } else if (ctx->lsb) {
        z3::expr lsbExpr = visit(ctx->lsb);
        currentContext->logstream << "FIXME: bit field selection " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
        bitSelWidth = freshConstant("bitsel$width", intSort);
    } else {
        // not selecting a slice
        currentContext->logstream << "visit arraysub index " << ctx->getText() << " at " << sourceLocation(ctx) << endl;

    }
    currentContext->logstream << "Fixme: array sub " << ctx->getText() << " z3 " << arrayExpr << " lsb expr "<< endl;
    // arrayExpr could be Bit#(n)
    // arrayExpr could be Array#(t)
    // arrayExpr could be Vector#(n, t)
    // return could be Bit#(1) or t
    z3::expr resultExpr = freshConstant("arraysub$", typeSort);
    z3::expr bitexprWidth = freshConstant("bitexpr$width", typeSort);
    z3::expr eltExpr = freshConstant("elt$", typeSort);
    z3::expr vsizeExpr = freshConstant("vsize$", typeSort);
    z3::expr bitselWidth = instantiateType("Bit", instantiateType("Numeric", bitSelWidth));
    z3::expr arraysubConstraint = ((arrayExpr == instantiateType("Bit", bitexprWidth) && resultExpr == bitselWidth)
                                   || (arrayExpr == instantiateType("Array", eltExpr) && resultExpr == eltExpr)
                                   || (arrayExpr == instantiateType("Vector", vsizeExpr, eltExpr) && resultExpr == eltExpr)
    );
    addConstraint(arraysubConstraint, ctx->getText(), ctx);
    z3::expr result = resultExpr;
    solver.push();
    if (checkSolution(ctx, true, true)) {
        shared_ptr<BSVType> resultType = modelValue(resultExpr);
        currentContext->logstream << "varinit result type is " << resultType->to_string() << " at " << sourceLocation(ctx) << endl;
        if (resultType->name == "Reg") {
            currentContext->logstream << "Reg type " << resultType->to_string() << " returning "
                                      << resultType->params[0]->to_string() << endl;

            resultType = resultType->params[0];
        }

        result = bsvTypeToExpr(resultType);
    }
    solver.pop();
    insertExpr(ctx, result);
    return result;
}

antlrcpp::Any TypeChecker::visitMemberbinds(BSVParser::MemberbindsContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitMemberbind(BSVParser::MemberbindContext *ctx) {
    z3::expr expr = visit(ctx->expression());
    insertExpr(ctx, expr);
    return expr;
}

antlrcpp::Any TypeChecker::visitInterfacestmt(BSVParser::InterfacestmtContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitBeginendblock(BSVParser::BeginendblockContext *ctx) {
    pushScope("beginend");
    visitChildren(ctx);
    popScope();
    return nullptr;
}

antlrcpp::Any TypeChecker::visitActionblock(BSVParser::ActionblockContext *ctx) {
    pushScope("actionblock");
    visitChildren(ctx);
    popScope();
    return nullptr;
}

antlrcpp::Any TypeChecker::visitActionvalueblock(BSVParser::ActionvalueblockContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    string name(freshString("actionvalueblock"));
    z3::expr avbExpr = constant(name, typeSort);
    pushScope("actionvalueblock");
    visitChildren(ctx);
    popScope();
    insertExpr(ctx, avbExpr);
    return avbExpr;
}

antlrcpp::Any TypeChecker::visitRegwrite(BSVParser::RegwriteContext *ctx) {
    z3::expr rhsExpr = visit(ctx->rhs);
    z3::expr lhsExpr = visit(ctx->lhs);
    z3::expr regExpr = instantiateType("Reg", rhsExpr);
    z3::expr constraint = (lhsExpr == regExpr);
    addConstraint(constraint, "reg$write", ctx);
    currentContext->logstream << "visit regwrite << " << constraint << endl;
    return nullptr;
}

antlrcpp::Any TypeChecker::visitStmt(BSVParser::StmtContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitIfstmt(BSVParser::IfstmtContext *ctx) {
    z3::expr condExpr = visit(ctx->expression());
    addConstraint(condExpr == instantiateType("Bool"), "condexpr$trk", ctx->expression());
    visit(ctx->stmt(0));
    if (ctx->stmt(1))
        visit(ctx->stmt(1));
    return nullptr;
}

antlrcpp::Any TypeChecker::visitCasestmt(BSVParser::CasestmtContext *ctx) {
    z3::expr expr = visit(ctx->expression());
    for (int i = 0; ctx->casestmtitem(i); i++) {
        BSVParser::CasestmtitemContext *item = ctx->casestmtitem(i);
        for (int j = 0; item->expression(j); j++) {
            z3::expr matchExpr = visit(item->expression(j));
            addConstraint(expr == matchExpr, "match$trk", item->expression(j));
        }
        visit(item->stmt());
    }
    for (int i = 0; ctx->casestmtpatitem(i); i++) {
        BSVParser::CasestmtpatitemContext *patitem = ctx->casestmtpatitem(i);
        z3::expr patExpr = visit(patitem->pattern());
        addConstraint(expr == patExpr, "patmatch$trk", patitem->pattern());
        for (int j = 0; patitem->patterncond(j); j++)
            visit(patitem->patterncond(j));
        visit(patitem->stmt());
    }
    return nullptr;
}

antlrcpp::Any TypeChecker::visitCasestmtdefaultitem(BSVParser::CasestmtdefaultitemContext *ctx) {
    visit(ctx->stmt());
    return nullptr;
}

antlrcpp::Any TypeChecker::visitWhilestmt(BSVParser::WhilestmtContext *ctx) {
    z3::expr condExpr = visit(ctx->expression());
    addConstraint(condExpr == instantiateType("Bool"), "whilcond$trk", ctx->expression());
    visit(ctx->stmt());
    return nullptr;
}

antlrcpp::Any TypeChecker::visitForstmt(BSVParser::ForstmtContext *ctx) {
    pushScope("forstmt");
    visit(ctx->forinit());
    visit(ctx->fortest());
    visit(ctx->forincr());
    visit(ctx->stmt());
    popScope();
    return nullptr;
}

antlrcpp::Any TypeChecker::visitForinit(BSVParser::ForinitContext *ctx) {
    string varName = ctx->var->getText();
    shared_ptr<BSVType> varType = bsvtype(ctx->bsvtype());
    shared_ptr<Declaration> varDecl = make_shared<Declaration>(varName, varType);
    lexicalScope->bind(varName, varDecl);
    z3::expr varExpr = constant(varDecl->uniqueName, typeSort);
    z3::expr varTypeExpr = bsvTypeToExpr(varType);
    addConstraint(varTypeExpr == varExpr, "forinit$trk", ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitSimplevardeclassign(BSVParser::SimplevardeclassignContext *ctx) {
    string varName = ctx->var->getText();
    shared_ptr<BSVType> varType;
    if (ctx->bsvtype()) {
        varType = bsvtype(ctx->bsvtype());
    }
    shared_ptr<Declaration> varDecl = make_shared<Declaration>(varName, varType);
    z3::expr varExpr = constant(varDecl->uniqueName, typeSort);
    if (ctx->bsvtype()) {
        z3::expr varTypeExpr = bsvTypeToExpr(varType);
        addConstraint(varExpr == varTypeExpr, "vardecltype$trk", ctx);
    }
    z3::expr rhsExpr = visit(ctx->expression());
    addConstraint(varExpr == rhsExpr, "vardeclassign$trk", ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitFortest(BSVParser::FortestContext *ctx) {
    z3::expr testExpr = visit(ctx->expression());
    z3::expr boolExpr = instantiateType("Bool");
    addConstraint(testExpr == boolExpr, "fortest$trk", ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitForincr(BSVParser::ForincrContext *ctx) {
    visitChildren(ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitVarincr(BSVParser::VarincrContext *ctx) {
    string varName = ctx->lowerCaseIdentifier()->getText();
    shared_ptr<Declaration> varDecl = lookup(varName);
    assert(varDecl);
    z3::expr varExpr = constant(varDecl->uniqueName, typeSort);
    z3::expr exprExpr = visit(ctx->expression());
    addConstraint(varExpr == exprExpr, "varincr$trk", ctx);
    return nullptr;
}

antlrcpp::Any TypeChecker::visitPattern(BSVParser::PatternContext *ctx) {
    if (ctx->var != NULL) {
        string varName = ctx->var->getText();
        shared_ptr<Declaration> varDecl = make_shared<Declaration>(varName, make_shared<BSVType>());
        lexicalScope->bind(varName, varDecl);
        currentContext->logstream << "Visit pattern var " << ctx->var->getText() << endl;
        return constant(varDecl->uniqueName, typeSort);
    } else if (ctx->constantpattern() != NULL) {
        return visit(ctx->constantpattern());
    } else if (ctx->taggedunionpattern()) {
        return visit(ctx->taggedunionpattern());
    } else if (ctx->tuplepattern()) {
        return visit(ctx->tuplepattern());
    } else {
        currentContext->logstream << "Visit pattern wildcard " << ctx->getText() << endl;
        return freshConstant("wildcard", typeSort);
    }
}

antlrcpp::Any TypeChecker::visitConstantpattern(BSVParser::ConstantpatternContext *ctx) {
    //FIXME
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTaggedunionpattern(BSVParser::TaggedunionpatternContext *ctx) {
    if (ctx->upperCaseIdentifier() != NULL) {
        string tagname(ctx->upperCaseIdentifier()->getText());
        currentContext->logstream << "Visit pattern tag " <<  tagname << endl;

        string patname(freshString(tagname));
        z3::expr patsym = constant(patname, typeSort);

        vector<z3::expr> exprs;
        for (auto it = currentContext->enumtag.find(tagname); it != currentContext->enumtag.end() && it->first == tagname; ++it) {
            shared_ptr<Declaration> decl(it->second);
            currentContext->logstream << "Tag pattern " << tagname << " of type " << decl->name << endl;
            map<string, shared_ptr<BSVType>> bindings;
            shared_ptr<BSVType> freshDeclType = freshType(decl->bsvtype, bindings);
            currentContext->logstream << "Tag pattern freshDeclType " << freshDeclType->to_string() << endl;
            vector<z3::expr> and_exprs;
            and_exprs.push_back(patsym == bsvTypeToExpr(freshDeclType));
            if (ctx->pattern(0)) {
                currentContext->logstream << "tag pattern 0 " << ctx->pattern(0)->getText() << endl;
                shared_ptr<UnionDeclaration> unionDeclaration = decl->unionDeclaration();
                assert(unionDeclaration);
                shared_ptr<Declaration> memberDecl = unionDeclaration->lookupMember(tagname);
                assert(memberDecl);
                currentContext->logstream << "Tag pattern memberDecl " << memberDecl->name << " bsvtype "<< memberDecl->bsvtype->to_string() << endl;
                shared_ptr<BSVType> memberType = freshType(memberDecl->bsvtype, bindings);
                currentContext->logstream << "Tag pattern fresh memberType " << memberType->to_string() << endl;
                if (!ctx->lowerCaseIdentifier(0)) {
                    // tagged Tag .pat
                    z3::expr patExpr = visit(ctx->pattern(0));
                    z3::expr memberTypeExpr = bsvTypeToExpr(memberType);
                    currentContext->logstream << "   pat expr " << patExpr << " member type expr " << memberTypeExpr << endl;
                    and_exprs.push_back(patExpr == memberTypeExpr);
                } else {
                    assert(!ctx->lowerCaseIdentifier(0));
                }
            }
            exprs.push_back(andExprs(and_exprs));
        }

        addConstraint(orExprs(exprs), "tunion$pat", ctx);

        z3::expr patexpr = constant(patname, typeSort);
        insertExpr(ctx, patexpr);
        return patsym;
    }
    assert(0);
    return visitChildren(ctx);
}

antlrcpp::Any TypeChecker::visitTuplepattern(BSVParser::TuplepatternContext *ctx) {
    auto it = exprs.find(ctx);
    if (it != exprs.end())
        return it->second;

    z3::expr_vector patterns(context);
    for (int i = 0; ctx->pattern(i); i++) {
        patterns.push_back(visit(ctx->pattern(i)));
    }
    string constructor = "Tuple" + to_string(patterns.size());
    z3::expr tuplePatternExpr = instantiateType(constructor, patterns);
    currentContext->logstream << "tuple pattern " << constructor << " z3 " << tuplePatternExpr << endl;
    insertExpr(ctx, tuplePatternExpr);
    return tuplePatternExpr;
}

antlrcpp::Any TypeChecker::visitProvisos(BSVParser::ProvisosContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitProviso(BSVParser::ProvisoContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) {
    return nullptr;
}

antlrcpp::Any TypeChecker::visitAttrspec(BSVParser::AttrspecContext *ctx) {
    return nullptr;
}

shared_ptr<BSVType> TypeChecker::bsvtype(z3::expr v, z3::model mod) {
    //currentContext->logstream << "    " << v << " isint: " << v.is_int() << endl;
    if (v.is_int())
        return BSVType::create(v.to_string(), BSVType_Numeric, false);

    z3::sort v_sort = v.get_sort();
    Z3_sort z3_sort = (Z3_sort) v_sort;
    string name;
    int n = 0; // constructor number
    for (auto jt = typeRecognizers.cbegin(); jt != typeRecognizers.cend(); ++jt) {
        z3::func_decl recognizer = jt->second;
        z3::expr r = recognizer(v);
        try {
            z3::expr is = mod.eval(r, true);

            if (is.is_true()) {
                name = jt->first;
                //currentContext->logstream << recognizer.name() << " testing {" << jt->first << "} -> {" << recognizer(v) << "} " << is << endl;
                break;
            }
        } catch (z3::exception e) {
            currentContext->logstream << "z3::exception " << e << endl;
        }
        n++;
    }
    if (v.is_const()) {
        std::shared_ptr<BSVType> bsvt(new BSVType(name));
        //currentContext->logstream << " const type ";
        //bsvt->prettyPrint(currentContext->logstream);
        //currentContext->logstream << endl;
        return bsvt;
    }
    std::shared_ptr<BSVType> bsvt(new BSVType(name));
    if (name == "FreeVar") {
        // fixme
        string fvname = v.arg(0).to_string();
        bsvt->params.push_back(make_shared<BSVType>(fvname.substr(1, fvname.size() - 2)));
    } else if (v.is_app()) {
        z3::func_decl func_decl = v.decl();
        size_t num_args = v.num_args();
        for (size_t i = 0; i < num_args; i++)
            bsvt->params.push_back(bsvtype(v.arg(i), mod));
    }
    //currentContext->logstream << " app type: ";
    //bsvt->prettyPrint(currentContext->logstream);
    //currentContext->logstream << endl;
    return bsvt;
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::BsvtypeContext *ctx) {
    if (ctx->typeide() != NULL) {
        BSVParser::TypeideContext *typeide = ctx->typeide();
        assert(!typeide->pkg);
        if (typeide->typevar) {
            string varname = typeide->typevar->getText();

            //FIXME: could be numeric
            return make_shared<BSVType>(varname, BSVType_Symbolic, true);
        }

        string typeName = typeide->name->getText();
        if (false && typeName == "Action") {
            return make_shared<BSVType>("ActionValue", make_shared<BSVType>("Void"));
        }

        vector<shared_ptr<BSVType>> param_types;
        vector<BSVParser::BsvtypeContext *> params = ctx->bsvtype();
        for (int i = 0; i < params.size(); i++) {
            param_types.push_back(bsvtype(params[i]));
        }

        return make_shared<BSVType>(typeName, param_types);
    } else if (ctx->var != NULL) {
        //FIXME: could be numeric
        return make_shared<BSVType>(ctx->getText(), BSVType_Symbolic, true);
    } else if (ctx->typenat() != NULL) {
        return make_shared<BSVType>(ctx->getText(), BSVType_Numeric, false);
    } else if (ctx->bsvtype(0) != NULL) {
        // parenthesized bsvtype expr
        return bsvtype(ctx->bsvtype(0));
    } else {
        currentContext->logstream << "Unhandled bsvtype: " << ctx->getText() << endl;
        return make_shared<BSVType>("Unhandled");
    }
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::TypeformalContext *ctx) {
    return BSVType::create(ctx->typeide()->getText(),
                           (ctx->numeric != NULL ? BSVType_Numeric : BSVType_Symbolic),
                           true);
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::TypedeftypeContext *ctx) {
    BSVParser::TypeideContext *typeide = ctx->typeide();
    assert(!typeide->pkg);
    string name(typeide->name != 0 ? typeide->name->getText() : typeide->typevar->getText());
    vector<shared_ptr<BSVType>> params;
    if (ctx->typeformals() != 0) {
        vector<BSVParser::TypeformalContext *> formals = ctx->typeformals()->typeformal();
        for (int i = 0; i < formals.size(); i++)
            params.push_back(bsvtype(formals[i]));
    }
    return BSVType::create(name, params);
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::FunctionprotoContext *ctx) {
    if (!ctx->bsvtype()) {
        cerr << "function proto with no return type " << ctx->name->getText() << " at " << sourceLocation(ctx) << endl;
    }
    shared_ptr<BSVType> returnType = bsvtype(ctx->bsvtype());
    vector<shared_ptr<BSVType>> params;
    vector<BSVParser::MethodformalContext *> mpfs;
    if (ctx->methodformals()) {
        mpfs = ctx->methodformals()->methodformal();
    }

    if (mpfs.size() == 0) {
        // special case, no arguments => type of method is return type
        currentContext->logstream << "parsed arity 0 functionproto type: " << ctx->getText() << endl;
        returnType->prettyPrint(currentContext->logstream);
        currentContext->logstream << endl;
        return returnType;
    }

    for (int i = 0; i < mpfs.size(); i++) {
        params.push_back(bsvtype(mpfs[i]));
    }

    params.push_back(returnType);
    string function = "Function" + to_string(params.size());
    shared_ptr<BSVType> functionType = BSVType::create(function, params);
    currentContext->logstream << "parsed function type: " << ctx->getText() << endl;
    functionType->prettyPrint(currentContext->logstream);
    currentContext->logstream << endl;
    return functionType;
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::MethodprotoformalContext *ctx) {
    if (ctx->bsvtype()) {
        return bsvtype(ctx->bsvtype());
    } else {
        currentContext->logstream << "unhandled: need to fill in the type from somewhere " << ctx->getText() << endl;
        return BSVType::create("Unspecified");
    }
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::MethodprotoContext *ctx) {
    shared_ptr<BSVType> returnType = bsvtype(ctx->bsvtype());
    vector<shared_ptr<BSVType>> params;
    vector<BSVParser::MethodprotoformalContext *> mpfs;
    if (ctx->methodprotoformals()) {
        mpfs = ctx->methodprotoformals()->methodprotoformal();
    }

    if (mpfs.size() == 0) {
        // special case, no arguments => type of method is return type
        currentContext->logstream << "parsed arity 0 methodproto type: " << ctx->getText() << endl;
        returnType->prettyPrint(currentContext->logstream);
        currentContext->logstream << endl;
        return returnType;
    }

    for (int i = 0; i < mpfs.size(); i++) {
        params.push_back(bsvtype(mpfs[i]));
    }

    params.push_back(returnType);
    string function = "Function" + to_string(params.size());
    shared_ptr<BSVType> functionType = BSVType::create(function, params);
    currentContext->logstream << "parsed methodproto type: " << ctx->getText() << endl;
    functionType->prettyPrint(currentContext->logstream);
    currentContext->logstream << endl;
    return functionType;
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::MethodformalContext *ctx) {
    if (ctx->bsvtype()) {
        return bsvtype(ctx->bsvtype());
    } else {
        currentContext->logstream << "unhandled: need to fill in the type from somewhere " << ctx->getText() << endl;
        return BSVType::create("Unspecified");
    }
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::MethoddefContext *ctx) {
    if (ctx->bsvtype() == nullptr) {
        currentContext->logstream << "No return type for method " << ctx->name->getText() << " at " << sourceLocation(ctx);
        return make_shared<BSVType>();
    }
    shared_ptr<BSVType> returnType = bsvtype(ctx->bsvtype());
    vector<shared_ptr<BSVType>> params;
    if (ctx->methodformals() == 0) {
        currentContext->logstream << "parsed arity 0 method return type: " << ctx->getText() << " at " << sourceLocation(ctx) << endl;
        return returnType;
    }

    vector<BSVParser::MethodformalContext *> mpfs = ctx->methodformals()->methodformal();
    for (int i = 0; i < mpfs.size(); i++) {
        params.push_back(bsvtype(mpfs[i]));
    }

    params.push_back(returnType);
    string function = "Function" + to_string(params.size());
    shared_ptr<BSVType> functionType = BSVType::create(function, params);
    currentContext->logstream << "parsed method type: " << ctx->getText() << endl;
    functionType->prettyPrint(currentContext->logstream);
    currentContext->logstream << " at " << sourceLocation(ctx) << endl;
    return functionType;

}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::ModuleprotoContext *ctx) {
    shared_ptr<BSVType> moduleInterface = make_shared<BSVType>("Module", bsvtype(ctx->moduleinterface));
    vector<shared_ptr<BSVType>> paramTypes;
    if (ctx->moduleprotoformals()) {
        vector<BSVParser::ModuleprotoformalContext *> moduleprotoformal = ctx->moduleprotoformals()->moduleprotoformal();
        for (int i = 0; i < moduleprotoformal.size(); i++)
            paramTypes.push_back(bsvtype(moduleprotoformal[i]));
        paramTypes.push_back(moduleInterface);
        string moduleConstructorName = "Function" + to_string(paramTypes.size());
        return make_shared<BSVType>(moduleConstructorName, paramTypes);
    } else {
        return moduleInterface;
    }
}

shared_ptr<BSVType> TypeChecker::bsvtype(BSVParser::ModuleprotoformalContext *ctx) {
    return bsvtype(ctx->bsvtype());
}

z3::expr TypeChecker::instantiateType(z3::func_decl type_decl, const z3::expr_vector &params) {
    if (type_decl.arity() != params.size()) {
        currentContext->logstream << "Mismatched params length " << params.size() << " for type " << type_decl
                                  << " expected " << type_decl.arity() << endl;
    }
    int error = context.check_error();
    if (error != Z3_OK)
        currentContext->logstream << "z3 error ? " << error << endl;
    return type_decl(params);
}

z3::expr TypeChecker::instantiateType(const string &type_name, const z3::expr_vector &params) {
    auto it = typeDecls.find(type_name);
    if (it == typeDecls.cend()) {
        currentContext->logstream << "No type constructor for " << type_name << endl;
    }
    assert(it != typeDecls.cend());
    z3::func_decl type_decl = it->second;
    if (type_decl.arity() != params.size())
        currentContext->logstream << "Unhandled type arity " << params.size() << " for type " << type_decl << endl;

    return type_decl(params);
}

z3::expr TypeChecker::instantiateType(const string &type_name) {
    z3::expr_vector params(context);
    return instantiateType(type_name, params);
}

z3::expr TypeChecker::instantiateType(const string &type_name, const z3::expr &param0) {
    z3::expr_vector params(context);
    params.push_back(param0);
    return instantiateType(type_name, params);
}

z3::expr TypeChecker::instantiateType(const string &type_name, const z3::expr &param0, const z3::expr &param1) {
    z3::expr_vector params(context);
    params.push_back(param0);
    params.push_back(param1);
    return instantiateType(type_name, params);
}

z3::expr TypeChecker::bsvTypeToExprHelper(shared_ptr<BSVType> bsvtype) {
    if (bsvtype->isVar) {
        string bsvname = bsvtype->name;
        string exprName = bsvname;
        return constant(exprName, typeSort);
    } else if (bsvtype->isNumeric()) {
        return instantiateType("Numeric", context.int_val((int) strtol(bsvtype->name.c_str(), NULL, 0)));
    } else if (bsvtype->name == "Numeric") {
        // special case
        return instantiateType("Numeric", context.int_val((int) strtol(bsvtype->params[0]->name.c_str(), NULL, 0)));
    } else if (bsvtype->name == "FreeVar") {
        // special case
        return instantiateType("FreeVar", context.string_val(bsvtype->params[0]->name));
    } else {
        z3::expr_vector arg_exprs(context);
        for (int i = 0; i < bsvtype->params.size(); i++) {
            arg_exprs.push_back(bsvTypeToExprHelper(bsvtype->params[i]));
        }
        bool foundDecl = typeDecls.find(bsvtype->name) != typeDecls.cend();
        bool found2 = currentContext->typeDeclaration.find(bsvtype->name) != currentContext->typeDeclaration.cend();

        currentContext->logstream << " looking up type constructor for " << bsvtype->name
                                  << (foundDecl ? " found" : " missing")
                                  << (found2 ? " found2" : " missing2")
                                  << endl;
        z3::func_decl typeDecl = typeDecls.find(bsvtype->name)->second;
        currentContext->logstream << " typeDecl " << typeDecl << endl;

        return instantiateType(typeDecl, arg_exprs);
    }
}

z3::expr TypeChecker::bsvTypeToExpr(shared_ptr<BSVType> bsvtype) {
    shared_ptr<BSVType> derefType = dereferenceType(bsvtype);
    return bsvTypeToExprHelper(derefType);
}


shared_ptr<BSVType> TypeChecker::freshType(const shared_ptr<BSVType> &bsvtype) {
    map<string, shared_ptr<BSVType>> bindings;
    return freshType(bsvtype, bindings);
}

shared_ptr<BSVType> TypeChecker::freshType(const shared_ptr<BSVType> &bsvtype, map<string, shared_ptr<BSVType>> &bindings) {
    if (bsvtype->isVar) {
        auto it = bindings.find(bsvtype->name);
        if (it == bindings.cend()) {
            shared_ptr<BSVType> fv = make_shared<BSVType>(freshString(bsvtype->name), bsvtype->kind, bsvtype->isVar);
            bindings[bsvtype->name] = fv;
            return fv;
        } else {
            return it->second;
        }
    } else {
        vector<shared_ptr<BSVType>> freshParams;
        for (int i = 0; i < bsvtype->params.size(); i++) {
            freshParams.push_back(freshType(bsvtype->params[i], bindings));
        }
        return make_shared<BSVType>(bsvtype->name, bsvtype->kind, bsvtype->isVar, freshParams);
    }
}
