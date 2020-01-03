

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
    for (int i = 0; i < decl->tags.size(); i++) {
        shared_ptr<Declaration> tagdecl = decl->tags[i];
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

void PackageContext::visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl) {
    assert(0);
}

void PackageContext::visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl) {
    declaration[decl->name] = decl;
    declarationList.push_back(decl);
}

void PackageContext::visitStructDeclaration(const shared_ptr<StructDeclaration> &decl) {
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
    for (int i = 0; i < decl->members.size(); i++) {
        shared_ptr<Declaration> member = decl->members[i];
        memberDeclaration.insert(make_pair(member->name, member));
    }
}

void PackageContext::visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl) {
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
}

void PackageContext::visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl) {
    logstream << "package context union " << decl->name << endl;
    typeDeclarationList.push_back(decl);
    typeDeclaration[decl->name] = decl;
    for (int i = 0; i < decl->members.size(); i++) {
        shared_ptr<Declaration> member = decl->members[i];
        memberDeclaration.insert(make_pair(member->name, member));
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
            std::shared_ptr<Declaration> constructorDecl = make_shared<Declaration>(constructorName, interfaceType,
                                                                                    GlobalBindingType);
            currentContext->logstream << "adding constructor: " << constructorName << endl;
            currentContext->typeDeclarationList.push_back(constructorDecl);
            currentContext->typeDeclaration[constructorName] = constructorDecl;
        }
    }
}

void TypeChecker::setupZ3Context() {
    context;
    exprs.clear();
    trackers.clear();
    typeDecls.clear();

    intSort = context.int_sort();
    boolSort = context.bool_sort();

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


    Z3_constructor default_constructors[] = {
            bozo_con,
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
        //fprintf(stderr, "User defined type %s predicate %s arity %d\n", typeDecl->name.c_str(), typePredicate.c_str(), arity);

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
    currentContext->logstream << "  insert expr " << ctx->getText().c_str() << endl;
    exprs.insert(std::pair<antlr4::ParserRuleContext *, z3::expr>(ctx, expr));
}

void TypeChecker::addConstraint(z3::expr constraint, const string &trackerPrefix, antlr4::ParserRuleContext *ctx) {
    currentContext->logstream << "  insert tracker " << ctx->getText().c_str() << endl;
    string trackerName(freshString(trackerPrefix));

    solver.add(constraint, trackerName.c_str());
    trackers.insert(std::pair<string, antlr4::ParserRuleContext *>(trackerName, ctx));
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

shared_ptr<BSVType> TypeChecker::dereferenceType(const shared_ptr<BSVType> &bsvtype) {
    if (bsvtype->isVar || bsvtype->isNumeric())
        return bsvtype;

    shared_ptr<BSVType> derefType = bsvtype;
    auto it = currentContext->typeDeclaration.find(bsvtype->name);
    if (it != currentContext->typeDeclaration.cend()) {
        shared_ptr<Declaration> decl = it->second;
        shared_ptr<TypeSynonymDeclaration> synonymDecl = decl->typeSynonymDeclaration();
        currentContext->logstream << "dereferencing bsvtype " << bsvtype->name << " found " << decl->name << endl;
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
        // handled later?
    } else if (pkgstmt->exportdecl()) {
        // handled later?
    } else {
        currentContext->logstream << "addDeclaration: unhandled package stmt at " << sourceLocation(pkgstmt) << endl;
        assert(0);
    }
}

void TypeChecker::addDeclaration(BSVParser::InterfacedeclContext *ctx) {
    shared_ptr<BSVType> interfaceType(bsvtype(ctx->typedeftype()));
    string name(interfaceType->name);

    int arity = interfaceType->params.size();

    currentContext->logstream << "add decl interface type : ";
    interfaceType->prettyPrint(currentContext->logstream);
    currentContext->logstream << " arity " << arity << endl;

    shared_ptr<InterfaceDeclaration> decl(new InterfaceDeclaration(name, interfaceType));
    currentContext->typeDeclarationList.push_back(decl);
    currentContext->typeDeclaration[name] = decl;
    lexicalScope->bind(name, decl);

    auto members = ctx->interfacememberdecl();
    for (int i = 0; i < members.size(); i++) {
        shared_ptr<Declaration> memberDecl((Declaration *) visitInterfacememberdecl(members[i]));

        currentContext->logstream << " subinterface decl " << memberDecl->name << endl;
        currentContext->memberDeclaration.emplace(memberDecl->name, memberDecl);
        memberDecl->parent = decl;
        decl->members.push_back(memberDecl);
    }
}

void TypeChecker::addDeclaration(BSVParser::FunctiondefContext *functiondef) {

}

void TypeChecker::addDeclaration(BSVParser::ModuledefContext *module) {

}

void TypeChecker::addDeclaration(BSVParser::TypeclassdeclContext *typeclassdecl) {
    currentContext->logstream << "visit type class decl " << typeclassdecl->typeclasside(0)->getText() << " at " << sourceLocation(typeclassdecl) << endl;
}

void TypeChecker::addDeclaration(BSVParser::TypeclassinstanceContext *typeclassinstance) {
    currentContext->logstream << "visit typeclass instance at " << sourceLocation(typeclassinstance) << endl;
}

void TypeChecker::addDeclaration(BSVParser::TypedefenumContext *ctx) {
    BSVParser::UpperCaseIdentifierContext *id = ctx->upperCaseIdentifier();
    string name(id->getText());
    shared_ptr<BSVType> bsvtype(new BSVType(name));
    shared_ptr<EnumDeclaration> decl(new EnumDeclaration(name, bsvtype));
    parentDecl = decl;
    lexicalScope->bind(name, decl);

    size_t numelts = ctx->typedefenumelement().size();
    for (size_t i = 0; i < numelts; i++) {
        BSVParser::TypedefenumelementContext *elt = ctx->typedefenumelement().at(i);
        if (elt) {
            currentContext->logstream << "enum elt " << elt->getText() << endl;
            shared_ptr<Declaration> subdecl = visit(elt);
            subdecl->parent = decl;
        }
    }
    currentContext->visitEnumDeclaration(decl);
}

void TypeChecker::addDeclaration(BSVParser::TypedefstructContext *structdef) {
    shared_ptr<BSVType> typedeftype(bsvtype(structdef->typedeftype()));
    string name = typedeftype->name;
    currentContext->logstream << "visit typedef struct " << name << endl;
    shared_ptr<StructDeclaration> structDecl(new StructDeclaration(name, typedeftype));
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
    shared_ptr<TypeSynonymDeclaration> synonymDecl = make_shared<TypeSynonymDeclaration>(typedeftype->name,
                                                                                         lhstype, typedeftype);
    currentContext->typeDeclaration[typedeftype->name] = synonymDecl;
    currentContext->typeDeclarationList.push_back(synonymDecl);
    lexicalScope->bind(typedeftype->name, synonymDecl);
}

void TypeChecker::addDeclaration(BSVParser::TypedeftaggedunionContext *uniondef) {
    shared_ptr<BSVType> typedeftype(bsvtype(uniondef->typedeftype()));
    string name = typedeftype->name;
    shared_ptr<UnionDeclaration> unionDecl(new UnionDeclaration(name, typedeftype));
    currentContext->logstream << "visit typedef union " << name << endl;
    for (int i = 0; uniondef->unionmember(i); i++) {
        shared_ptr<Declaration> subdecl = visit(uniondef->unionmember(i));
        unionDecl->members.push_back(subdecl);
    }
    currentContext->visitUnionDeclaration(unionDecl);
    shared_ptr<Declaration> decl = unionDecl;
    lexicalScope->bind(name, decl);
}


void TypeChecker::addDeclaration(BSVParser::VarbindingContext *varbinding) {

}


