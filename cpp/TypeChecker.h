#pragma once

#include <assert.h>

#include <map>
#include <iostream>
#include "antlr4-runtime.h"
#include "z3++.h"
#include "z3_api.h"
#include "z3.h"

#include "BSVBaseVisitor.h"
#include "Declaration.h"
#include "LexicalScope.h"

using namespace std;

class PackageContext {
public:
    vector<shared_ptr<Declaration> > declarationList;
    vector<shared_ptr<Declaration> > typeDeclarationList;
    map<string, shared_ptr<Declaration> > declaration;
    map<string, shared_ptr<Declaration> > typeDeclaration;
    multimap<string, shared_ptr<Declaration> > enumtag;
    multimap<string, shared_ptr<Declaration> > memberDeclaration;

    void import(const shared_ptr<LexicalScope> &scope);

    void visitEnumDeclaration(const shared_ptr<EnumDeclaration> &decl);
    void visitInterfaceDeclaration(const shared_ptr<InterfaceDeclaration> &decl);
    void visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl);
    void visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl);
    void visitStructDeclaration(const shared_ptr<StructDeclaration> &decl);
    void visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl);
    void visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl);
};

/**
 * Static analyzer of BSV package
 */
class TypeChecker : public BSVBaseVisitor {

    // Z3 Solver information, reset when processing each module definition
    z3::context context;
    z3::solver solver;
    map<antlr4::ParserRuleContext *, z3::expr> exprs;
    map<string, antlr4::ParserRuleContext *> trackers;
    map<antlr4::ParserRuleContext *, shared_ptr<BSVType>> exprTypes;
    map<antlr4::ParserRuleContext *, shared_ptr<Declaration>> varDecls;
    map<string, z3::func_decl> typeDecls;
    map<string, z3::func_decl> typeRecognizers;
    z3::sort typeSort, intSort, boolSort;

    map<string, bool> boolops;

    shared_ptr<LexicalScope> lexicalScope;
    map<string, shared_ptr<LexicalScope>> packageScopes;
    shared_ptr<PackageContext> currentContext;

    bool actionContext;
    shared_ptr<Declaration> parentDecl;
    int nameCount;
    const vector<string> includePath;
public:
    TypeChecker(const vector<string> &includePath)
            : context(), solver(context), typeSort(context), intSort(context), boolSort(context), nameCount(100),
              actionContext(false), includePath(includePath) {
        //solver.set("produce-unsat-cores", true);
        z3::params p(context);
        // enable unsat core tracking
        p.set("unsat_core", true);
        solver.set(p);
        lexicalScope = make_shared<LexicalScope>("<global>");
        currentContext = make_shared<PackageContext>();
        setupModuleFunctionConstructors();
    }

    shared_ptr<BSVType> lookup(antlr4::ParserRuleContext *ctx) {
        if (exprTypes.find(ctx) != exprTypes.cend())
            return exprTypes.find(ctx)->second;
        cerr << "no entry for " << ctx->getText() << " " << ctx->getText() << endl;
        return BSVType::create("NOENT");
    }

    BSVParser::PackagedefContext *analyzePackage(const string &packageName);

private:
    static const char *check_result_name[];

    string searchIncludePath(const string &pkgName);

    void setupZ3Context();

    void setupModuleFunctionConstructors();

    string freshString(string name);

    z3::symbol freshName(string name);

    z3::expr freshConstant(string name, z3::sort sort);

    z3::expr constant(string name, z3::sort sort);

    void insertExpr(antlr4::ParserRuleContext *ctx, z3::expr expr);

    void addConstraint(z3::expr constraint, const string &trackerPrefix, antlr4::ParserRuleContext *ctx);

    z3::expr orExprs(vector<z3::expr> exprs);

    void pushScope(const string &name) {
        lexicalScope = make_shared<LexicalScope>(name, lexicalScope);
    }

    void popScope() {
        lexicalScope = lexicalScope->parent;
    }

protected:

    virtual antlrcpp::Any visitPackagedef(BSVParser::PackagedefContext *ctx) override {
        size_t numelts = ctx->packagestmt().size();

        for (size_t i = 0; i < numelts; i++) {
            visit(ctx->packagestmt().at(i));
        }
        return freshConstant("pkgstmt", typeSort);
    }

    virtual antlrcpp::Any visitPackagedecl(BSVParser::PackagedeclContext *ctx) override {
        setupZ3Context();
        return freshConstant("pkgdecl", typeSort);
    }

    virtual antlrcpp::Any visitEndpackage(BSVParser::EndpackageContext *ctx) override {
        return freshConstant("endpkg", typeSort);
    }

    virtual antlrcpp::Any visitLowerCaseIdentifier(BSVParser::LowerCaseIdentifierContext *ctx) override {
        string varname(ctx->getText());
        return context.constant(context.str_symbol(varname.c_str()), typeSort);
    }

    virtual antlrcpp::Any visitUpperCaseIdentifier(BSVParser::UpperCaseIdentifierContext *ctx) override {
        cerr << "unhandled visitUpperCaseIdentifier: " << ctx->getText() << endl;
        assert(0);
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitAnyidentifier(BSVParser::AnyidentifierContext *ctx) override {
        cerr << "unhandled visitAnyidentifier: " << ctx->getText() << endl;
        assert(0);
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitExportdecl(BSVParser::ExportdeclContext *ctx) override {
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitExportitem(BSVParser::ExportitemContext *ctx) override {
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitImportdecl(BSVParser::ImportdeclContext *ctx) override {
        string pkgName = ctx->upperCaseIdentifier(0)->getText();
        cerr << "importing package " << pkgName << endl;
        analyzePackage(pkgName);
        shared_ptr<LexicalScope> pkgScope = packageScopes[pkgName];
        currentContext->import(pkgScope);
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitPackagestmt(BSVParser::PackagestmtContext *ctx) override {
        setupZ3Context();
        cerr << "visitPackagestmt at " << sourceLocation(ctx) << endl;
        cerr << "                    " << ctx->getText() << endl;
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackageide(BSVParser::PackageideContext *ctx) override {
        assert(0);
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitInterfacedecl(BSVParser::InterfacedeclContext *ctx) override {
        shared_ptr<BSVType> interfaceType(bsvtype(ctx->typedeftype()));
        string name(interfaceType->name);

        int arity = interfaceType->params.size();

        cerr << "interface type : ";
        interfaceType->prettyPrint(cerr);
        cerr << " arity " << arity << endl;

        shared_ptr<InterfaceDeclaration> decl(new InterfaceDeclaration(name, interfaceType));
        currentContext->typeDeclarationList.push_back(decl);
        currentContext->typeDeclaration[name] = decl;
        lexicalScope->bind(name, decl);

        auto members = ctx->interfacememberdecl();
        for (int i = 0; i < members.size(); i++) {
            shared_ptr<Declaration> memberDecl((Declaration *) visitInterfacememberdecl(members[i]));

            cerr << " subinterface decl " << memberDecl->name << endl;
            currentContext->memberDeclaration.emplace(memberDecl->name, memberDecl);
            memberDecl->parent = decl;
            decl->members.push_back(memberDecl);
        }
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) override {
        cerr << "visitInterfacememberdecl: " << ctx->getText() << endl;
        if (ctx->methodproto())
            return visit(ctx->methodproto());
        else if (ctx->subinterfacedecl())
            return visit(ctx->subinterfacedecl());
        return nullptr;
    }

    virtual antlrcpp::Any visitMethodproto(BSVParser::MethodprotoContext *ctx) override {
        shared_ptr<BSVType> methodType = bsvtype(ctx);
        cerr << "Visit method proto " << ctx->getText();
        if (methodType) {
            cerr << " : ";
            methodType->prettyPrint(cerr);
        }
        cerr << endl;
        return (Declaration *) new MethodDeclaration(ctx->name->getText(), methodType);
    }

    virtual antlrcpp::Any visitMethodprotoformals(BSVParser::MethodprotoformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodprotoformal(BSVParser::MethodprotoformalContext *formal) override {
        string formalName = formal->name->getText();
        lexicalScope->bind(formalName,
                           make_shared<Declaration>(formalName, make_shared<BSVType>(), MethodParamBindingType));
        cerr << "method proto formal " << formalName << endl;

        z3::expr formalExpr = context.constant(context.str_symbol(formalName.c_str()), typeSort);

        if (formal->bsvtype()) {
            z3::expr typeExpr = visit(formal->bsvtype());
            addConstraint(formalExpr == typeExpr, "mpf", formal);
            cerr << "method proto formal constraint: " << (formalExpr == typeExpr) << endl;
        } else {
            cerr << "visitMethodprotoFormal: fixme no type " << formalName << endl;
        }
        insertExpr(formal, formalExpr);
        return formalExpr;
    }

    virtual antlrcpp::Any visitSubinterfacedecl(BSVParser::SubinterfacedeclContext *ctx) override {
        cerr << "visit subinterfacedecl " << ctx->getText() << endl;
        string name(ctx->lowerCaseIdentifier()->getText());
        shared_ptr<BSVType> subinterfaceType(bsvtype(ctx->bsvtype()));
        Declaration *subinterfaceDecl = new InterfaceDeclaration(name, subinterfaceType);
        return subinterfaceDecl;
    }

    virtual antlrcpp::Any visitTypedeftype(BSVParser::TypedeftypeContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeformals(BSVParser::TypeformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeformal(BSVParser::TypeformalContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefsynonym(BSVParser::TypedefsynonymContext *ctx) override {
        shared_ptr<BSVType> lhstype = bsvtype(ctx->bsvtype());
        shared_ptr<BSVType> typedeftype = bsvtype(ctx->typedeftype());
        cerr << "visit typedef synonym " << typedeftype->name << endl;
        shared_ptr<TypeSynonymDeclaration> synonymDecl = make_shared<TypeSynonymDeclaration>(typedeftype->name,
                                                                                             lhstype, typedeftype);
        currentContext->typeDeclaration[typedeftype->name] = synonymDecl;
        currentContext->typeDeclarationList.push_back(synonymDecl);
        lexicalScope->bind(typedeftype->name, synonymDecl);

        return synonymDecl;
    }

    virtual antlrcpp::Any visitTypedefenum(BSVParser::TypedefenumContext *ctx) override {
        BSVParser::UpperCaseIdentifierContext *id = ctx->upperCaseIdentifier();
        string name(id->getText());
        shared_ptr<BSVType> bsvtype(new BSVType(name));
        shared_ptr<Declaration> decl(new EnumDeclaration(name, bsvtype));
        parentDecl = decl;
        currentContext->typeDeclaration[name] = decl;
        lexicalScope->bind(name, decl);

        size_t numelts = ctx->typedefenumelement().size();
        for (size_t i = 0; i < numelts; i++) {
            BSVParser::TypedefenumelementContext *elt = ctx->typedefenumelement().at(i);
            fprintf(stderr, "elt %p\n", elt);
            if (elt) {
                fprintf(stderr, "elt %s\n", elt->getText().c_str());

                visit(elt);
            }
        }

        return decl;
    }

    virtual antlrcpp::Any visitTypedefenumelement(BSVParser::TypedefenumelementContext *ctx) override {
        BSVParser::UpperCaseIdentifierContext *tag = ctx->tag;
        string name(tag->getText());
        shared_ptr<BSVType> bsvtype(new BSVType(name));
        shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
        //declarationList.push_back(decl);
        currentContext->enumtag.insert(make_pair(name, parentDecl));
        return decl;
    }

    virtual antlrcpp::Any visitTypedefstruct(BSVParser::TypedefstructContext *ctx) override {
        BSVParser::TypedeftypeContext *typedeftype = ctx->typedeftype();
        string name(typedeftype->getText());
        shared_ptr<BSVType> bsvtype(new BSVType(name));
        shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
        currentContext->typeDeclarationList.push_back(decl);
        currentContext->typeDeclaration[name] = decl;
        lexicalScope->bind(name, decl);
        return decl;
    }

    virtual antlrcpp::Any visitTypedeftaggedunion(BSVParser::TypedeftaggedunionContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStructmember(BSVParser::StructmemberContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUnionmember(BSVParser::UnionmemberContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubstruct(BSVParser::SubstructContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubunion(BSVParser::SubunionContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitDerives(BSVParser::DerivesContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarbinding(BSVParser::VarbindingContext *ctx) override {
        BindingType bindingType = lexicalScope->isGlobal() ? GlobalBindingType : LocalBindingType;
        vector<BSVParser::VarinitContext *> varinits = ctx->varinit();
        for (size_t i = 0; i < varinits.size(); i++) {
            BSVParser::VarinitContext *varinit = varinits[i];
            string varName = varinit->var->getText();
            shared_ptr<Declaration> varDecl = make_shared<Declaration>(varName, make_shared<BSVType>(), bindingType);
            lexicalScope->bind(varName, varDecl);

            z3::expr lhsexpr = visit(varinit->var);
            if (ctx->t) {
                z3::expr bsvtypeExpr = visit(ctx->t);
                addConstraint(lhsexpr == bsvtypeExpr, "varbindingt", varinit);
            }
            if (varinit->rhs) {
                cerr << "visit VarInit rhs " << varinit->rhs->getText() << endl;
                z3::expr rhsexpr = visit(varinit->rhs);
                addConstraint(lhsexpr == rhsexpr, "varinit", varinit);
            } else {
                cerr << "varinit with no rhs " << varinit->getText() << endl;
            }
        }
        return nullptr;
    }

    virtual antlrcpp::Any visitActionbinding(BSVParser::ActionbindingContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        fprintf(stderr, "        TypeChecker visiting action binding %s\n", ctx->getText().c_str());

        string varname(ctx->var->getText().c_str());
        BindingType bindingType = lexicalScope->isGlobal() ? GlobalBindingType : LocalBindingType;
        lexicalScope->bind(varname, make_shared<Declaration>(varname, make_shared<BSVType>(), bindingType));
        z3::expr varsym = context.constant(context.str_symbol(varname.c_str()), typeSort);

        if (ctx->bsvtype()) {
            z3::expr interfaceType = visit(ctx->bsvtype());
            cerr << "action binding constraint " << (interfaceType == varsym) << endl;
            addConstraint(interfaceType == varsym, "actionbindingt", ctx);
        }
        z3::expr rhstype = visit(ctx->rhs);
        z3::expr lhstype = instantiateType("Module", varsym);
        addConstraint(lhstype == rhstype, "actionbinding", ctx);
        cerr << "action binding rhs constraint " << (lhstype == rhstype) << endl;
        insertExpr(ctx, varsym);
        return varsym;
    }

    virtual antlrcpp::Any visitPatternbinding(BSVParser::PatternbindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeclassdecl(BSVParser::TypeclassdeclContext *ctx) override {
        cerr << "visit type class decl " << ctx->typeclasside(0)->getText() << " at " << sourceLocation(ctx) << endl;
        return nullptr;
    }

    virtual antlrcpp::Any visitTypeclasside(BSVParser::TypeclassideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedepends(BSVParser::TypedependsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedepend(BSVParser::TypedependContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypelist(BSVParser::TypelistContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitOverloadeddecl(BSVParser::OverloadeddeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTctype(BSVParser::TctypeContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeclassinstance(BSVParser::TypeclassinstanceContext *ctx) override {
        cerr << "visit typeclass instance at " << sourceLocation(ctx) << endl;
        return nullptr;
    }

    virtual antlrcpp::Any visitOverloadeddef(BSVParser::OverloadeddefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuledef(BSVParser::ModuledefContext *ctx) override {

        string module_name = ctx->moduleproto()->name->getText();
        shared_ptr<BSVType> moduleType(bsvtype(ctx->moduleproto()));
        cerr << "tc ModuleDef " << module_name << " : ";
        moduleType->prettyPrint(cerr);
        cerr << endl;

        // declare the module in the global scope
        shared_ptr<ModuleDefinition> moduleDefinition = ModuleDefinition::create(module_name, moduleType);
        currentContext->declaration[module_name] = moduleDefinition;
        currentContext->declarationList.push_back(moduleDefinition);
        lexicalScope->bind(module_name, moduleDefinition);

        // then setup the scope for the body of the module
        setupZ3Context();
        pushScope(module_name);
        solver.push();

        visit(ctx->moduleproto());

        //vector<BSVParser::ModulestmtContext *> stmts = ctx->modulestmt();
        for (int i = 0; ctx->modulestmt(i); i++) {
            cerr << "module stmt " << ctx->modulestmt(i)->getText() << endl;
            visit(ctx->modulestmt(i));
        }
        z3::check_result checked = solver.check();
        fprintf(stderr, "  Type checking module %s: %s\n", module_name.c_str(), check_result_name[checked]);
        cerr << solver << endl;
        if (checked == z3::sat) {
            z3::model mod = solver.get_model();
            cerr << "model: " << mod << endl;
            cerr << exprs.size() << " exprs" << endl;
            for (auto it = exprs.cbegin(); it != exprs.cend(); ++it) {
                z3::expr e = it->second;
                try {
                    z3::expr v = mod.eval(e, true);
                    cerr << e << " evaluates to " << v << " is datatype " << v.is_datatype() << endl;
                    exprTypes[it->first] = bsvtype(v, mod);
                } catch (const exception &e) {
                    cerr << "exception" << endl;
                }
            }
        } else {
            z3::expr_vector unsat_core = solver.unsat_core();
            cerr << "unsat_core " << unsat_core << endl;
            cerr << "unsat_core.size " << unsat_core.size() << endl;
            for (int i = 0; i < unsat_core.size(); i++) {
                z3::expr e = unsat_core[i];
                cerr << e << endl;
            }
        }
        solver.pop();
        popScope();
        return moduleDefinition;
    }

    virtual antlrcpp::Any visitModuleproto(BSVParser::ModuleprotoContext *ctx) override {
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
            cerr << "module proto type " << ctx->name->getText() << " z3::expr " << moduleProtoType << endl;
            return moduleProtoType;
        } else {
            return moduleInterface;
        }
    }

    virtual antlrcpp::Any visitModuleprotoformals(BSVParser::ModuleprotoformalsContext *ctx) override {
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

    virtual antlrcpp::Any visitModuleprotoformal(BSVParser::ModuleprotoformalContext *formal) override {
        string formalName = formal->name->getText();
        lexicalScope->bind(formalName,
                           make_shared<Declaration>(formalName, make_shared<BSVType>(), ModuleParamBindingType));

        z3::expr formalExpr = context.constant(context.str_symbol(formalName.c_str()), typeSort);
        if (formal->bsvtype()) {
            z3::expr typeExpr = visit(formal->bsvtype());
            addConstraint(formalExpr == typeExpr, "mpf", formal);
            cerr << "method proto formal constraint: " << (formalExpr == typeExpr) << endl;
        } else {
            cerr << "visitMethodprotoFormal: fixme no type " << formal->name->getText() << endl;
        }
        insertExpr(formal, formalExpr);
        return formalExpr;
    }

    virtual antlrcpp::Any visitModulestmt(BSVParser::ModulestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleinst(BSVParser::ModuleinstContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethoddef(BSVParser::MethoddefContext *ctx) override {
        string methodName(ctx->name->getText().c_str());
        cerr << "    tc MethodDef " << methodName << endl;
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
        return new MethodDefinition(ctx->name->getText(), methodType);
    }

    virtual antlrcpp::Any visitMethodformals(BSVParser::MethodformalsContext *ctx) override {
        vector<BSVParser::MethodformalContext *> formals = ctx->methodformal();
        for (int i = 0; i < formals.size(); i++) {
            visit(formals[i]);
        }
        return 0;
    }

    virtual antlrcpp::Any visitMethodformal(BSVParser::MethodformalContext *formal) override {
        string formalName = formal->lowerCaseIdentifier()->getText();
        lexicalScope->bind(formalName,
                           make_shared<Declaration>(formalName, make_shared<BSVType>(), MethodParamBindingType));
        cerr << "method formal " << formalName << endl;

        z3::expr formalExpr = context.constant(context.str_symbol(formalName.c_str()), typeSort);
        if (formal->bsvtype()) {
            z3::expr typeExpr = visit(formal->bsvtype());
            addConstraint(formalExpr == typeExpr, "methodformalt", formal);
            cerr << "method formal constraint: " << (formalExpr == typeExpr) << endl;
        } else {
            cerr << "visitMethodFormal: fixme no type " << formalName << endl;
        }
        insertExpr(formal, formalExpr);
        return formalExpr;
    }

    virtual antlrcpp::Any visitMethodcond(BSVParser::MethodcondContext *ctx) override {
        z3::expr condtype = visit(ctx->expression());
        z3::func_decl boolcon = typeDecls.find("Bool")->second;
        addConstraint(condtype == boolcon(), "methodcond", ctx);
        return condtype;
    }

    virtual antlrcpp::Any visitSubinterfacedef(BSVParser::SubinterfacedefContext *ctx) override {
        if (ctx->expression()) {
            //FIXME:
            visit(ctx->expression());
        } else {
            cerr << "visitSubinterfacedef " << ctx->upperCaseIdentifier()->getText() << endl;
            vector<BSVParser::InterfacestmtContext *> stmts = ctx->interfacestmt();
            for (int i = 0; i < stmts.size(); i++) {
                visit(stmts[i]);
            }
        }
        return 0;
    }

    virtual antlrcpp::Any visitRuledef(BSVParser::RuledefContext *ctx) override {
        fprintf(stderr, "    tc RuleDef %s\n", ctx->name->getText().c_str());
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

    virtual antlrcpp::Any visitRulecond(BSVParser::RulecondContext *ctx) override {
        z3::expr condtype = visit(ctx->expression());
        z3::func_decl boolcon = typeDecls.find("Bool")->second;
        addConstraint(condtype == boolcon(), "rulecond", ctx);
        insertExpr(ctx, condtype);
        return condtype;
    }

    virtual antlrcpp::Any visitFunctiondef(BSVParser::FunctiondefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFunctionproto(BSVParser::FunctionprotoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExterncimport(BSVParser::ExterncimportContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExterncfuncargs(BSVParser::ExterncfuncargsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExterncfuncarg(BSVParser::ExterncfuncargContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarassign(BSVParser::VarassignContext *ctx) override {
        cerr << "var assign " << ctx->getText() << endl;
        z3::expr lhsExpr = visit(ctx->lvalue(0));
        z3::expr rhsExpr = visit(ctx->expression());
        //FIXME: module instance or action binding
        addConstraint(lhsExpr == rhsExpr, "varassign", ctx);
        return visitChildren(ctx);
    }

    z3::expr visitLIndexValue(BSVParser::ExprprimaryContext *ctx, BSVParser::ExpressionContext *index) {
        cerr << "Visit array index lvalue at " << sourceLocation(ctx) << endl;

        z3::expr arrayExpr = visit(ctx);
        z3::expr indexExpr = visit(ctx);
        z3::expr typeexpr = freshConstant("alindex", typeSort);
        vector<z3::expr> exprs;
        exprs.push_back(typeexpr == instantiateType("Bit", instantiateType("Numeric", context.int_val(1))));
        exprs.push_back(arrayExpr == instantiateType("Vector",
                                                     instantiateType("Numeric", freshConstant("alindex", intSort)),
                                                     typeexpr));

        if (exprs.size())
            addConstraint(orExprs(exprs), "alindext", ctx);

        insertExpr(ctx, typeexpr);
        return typeexpr;
    }

    z3::expr visitLFieldValue(BSVParser::ExprprimaryContext *ctx, string fieldname) {
        cerr << "Visit field lvalue " << fieldname << endl;

        z3::expr sym = context.constant(context.str_symbol(fieldname.c_str()), typeSort);
        vector<z3::expr> exprs;
        for (auto it = currentContext->memberDeclaration.find(fieldname);
             it != currentContext->memberDeclaration.end() && it->first == fieldname; ++it) {
            shared_ptr<Declaration> memberDecl(it->second);
            shared_ptr<Declaration> interfaceDecl(memberDecl->parent);
            cerr << "    field " << fieldname << " belongs to type " << interfaceDecl->name << endl;
            //FIXME continue here
            z3::func_decl type_decl = typeDecls.find(interfaceDecl->name)->second;
            z3::expr type_expr = freshConstant("_ph_", typeSort);
            switch (type_decl.arity()) {
                case 0: {
                    type_expr = type_decl();
                }
                    break;
                case 1: {
                    z3::expr type_var = freshConstant("_var_", typeSort);
                    type_expr = type_decl(type_var);
                }
                    break;
                default:
                    cerr << "Unhandled type arity " << type_decl;
            }
            exprs.push_back(sym == type_expr);
        }
        if (exprs.size())
            addConstraint(orExprs(exprs), "fieldval", ctx);

        z3::expr fieldexpr = constant(fieldname, typeSort);
        insertExpr(ctx, fieldexpr);
        return fieldexpr;
    }

    virtual antlrcpp::Any visitLvalue(BSVParser::LvalueContext *ctx) override {
        if (BSVParser::ExprprimaryContext *lhs = ctx->exprprimary()) {
            z3::expr lhsExpr = visit(lhs);
            if (ctx->index != NULL) {
                // lvalue [ index ]
                return visitLIndexValue(lhs, ctx->index);
            } else if (ctx->lowerCaseIdentifier()) {
                // lvalue . field
                return visitLFieldValue(lhs, ctx->lowerCaseIdentifier()->getText());
            } else {
                // lvalue [ msb : lsb ]
                assert(0);
            }
        } else {
            BSVParser::LowerCaseIdentifierContext *id = ctx->lowerCaseIdentifier();
            //FIXME
            z3::expr varExpr = context.constant(context.str_symbol(id->getText().c_str()), typeSort);
            return varExpr;
        }
        cerr << "Unhandled lvalue " << ctx->getText() << endl;
        assert(0);
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBsvtype(BSVParser::BsvtypeContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;

        z3::expr bsvtype_expr(context);
        shared_ptr<BSVType> bbb(bsvtype(ctx));
        cerr << "typechecker::visitBsvtype " << ctx->getText() << " bbb ";
        bbb->prettyPrint(cerr);
        cerr << endl;

        if (!bbb->isNumeric()) {
            BSVParser::TypeideContext *typeide = ctx->typeide();
            if (typeide != NULL) {
                if (typeide->name) {
                    string name = bbb->name;
                    auto jt = typeDecls.find(name);
                    if (jt != typeDecls.end()) {
                        z3::func_decl decl = jt->second;
                        vector<BSVParser::BsvtypeContext *> typeArgs = ctx->bsvtype();
                        int numArgs = typeArgs.size();
                        switch (numArgs) {
                            case 0:
                                bsvtype_expr = decl();
                                break;
                            case 1: {
                                z3::expr t0 = visit(typeArgs[0]);
                                cerr << "func_decl " << decl << " t0 " << t0 << endl;
                                bsvtype_expr = decl(t0);
                            }
                                break;
                            case 2: {
                                z3::expr t0 = visit(typeArgs[0]);
                                z3::expr t1 = visit(typeArgs[1]);
                                cerr << "func_decl " << decl << " t0 " << t0 << " t1 " << t1 << endl;
                                bsvtype_expr = decl(t0, t1);
                            }
                                break;
                            default:
                                fprintf(stderr, "Too many type arguments: %d\n", numArgs);
                        }
                    } else {
                        cerr << "unhandled bsvtype_expr not in typeDecls " << bbb->name << " bozo " << endl;
                        z3::func_decl bozoDecl = typeDecls.find("Bozo")->second;
                        bsvtype_expr = bozoDecl();
                    }
                } else {
                    string name = typeide->typevar->getText();
                    //FIXME: numeric?
                    bsvtype_expr = constant(name, typeSort);
                }
            }
        } else if (ctx->typenat() != NULL) {
            return instantiateType("Numeric", context.int_val((int) strtol(ctx->getText().c_str(), NULL, 0)));
        } else {
            fprintf(stderr, "Unhandled bsvtype_expr %s\n", ctx->getText().c_str());
        }

        if (0) {
            solver.push();
            fprintf(stderr, "        check(%s) %s\n", ctx->getText().c_str(), check_result_name[solver.check()]);
            solver.pop();
        }

        insertExpr(ctx, bsvtype_expr);
        return bsvtype_expr;
    }

    virtual antlrcpp::Any visitTypeide(BSVParser::TypeideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypenat(BSVParser::TypenatContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitOperatorexpr(BSVParser::OperatorexprContext *ctx) override {
        return visit(ctx->binopexpr());
    }

    virtual antlrcpp::Any visitCaseexpr(BSVParser::CaseexprContext *ctx) override {
        fprintf(stderr, "visit case expr %s\n", ctx->getText().c_str());
        z3::expr casetype = freshConstant("case", typeSort);
        z3::expr exprtype = visit(ctx->expression());
        size_t numitems = ctx->caseexpritem().size();
        for (size_t i = 0; i < numitems; i++) {
            BSVParser::CaseexpritemContext *item = ctx->caseexpritem()[i];
            fprintf(stderr, "item = %p\n", item);
            if (item->body != NULL) {
                fprintf(stderr, "caseexpritem has pattern %s body %s\n",
                        item->pattern()->getText().c_str(),
                        item->body->getText().c_str());

                if (item->pattern() != NULL) {
                    z3::expr itemtype = visit(item->pattern());
                    addConstraint(exprtype == itemtype, "caseitem", item);
                }
                z3::expr bodytype = visit(item->body);
                addConstraint(casetype == bodytype, "casebody", item->body);
            }
        }
        return casetype;
    }

    virtual antlrcpp::Any visitMatchesexpr(BSVParser::MatchesexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCondexpr(BSVParser::CondexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCaseexpritem(BSVParser::CaseexpritemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPatterncond(BSVParser::PatterncondContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBinopexpr(BSVParser::BinopexprContext *ctx) override {

        if (ctx->unopexpr() != NULL)
            return visit(ctx->unopexpr());

        auto it = exprs.find(ctx);
        if (it != exprs.end()) {
            z3::expr result = it->second;
            fprintf(stderr, "        Re-Visit binop %s\n", ctx->getText().c_str());
            return result;
        }
        fprintf(stderr, "        Visit binop %s\n", ctx->getText().c_str());

        z3::expr leftsym = visit(ctx->left);
        z3::expr rightsym = visit(ctx->right);

        addConstraint(leftsym == rightsym, "binop", ctx);
        if (0) {
            solver.push();
            cerr << "  checking " << ctx->getText() << endl;
            //cerr << solver << endl;
            cerr << "        check(" << ctx->getText() << ") " << check_result_name[solver.check()] << endl;
            solver.pop();
        }


        string opstr(ctx->op->getText());
        char opnamebuf[128];
        snprintf(opnamebuf, sizeof(opnamebuf) - 1, "expr%s-%d", opstr.c_str(), nameCount++);
        string binopstr(opnamebuf);
        z3::expr binopsym = context.constant(binopstr.c_str(), typeSort);
        if (boolops.find(opstr) != boolops.end()) {
            fprintf(stderr, "Bool expr %s\n", ctx->getText().c_str());
            z3::func_decl Bool = typeDecls.find("Bool")->second;
            addConstraint(binopsym == Bool(), "binboolop", ctx);
        } else {
            fprintf(stderr, "Bit expr %s\n", ctx->getText().c_str());
            z3::func_decl Bit = typeDecls.find("Bit")->second;
            string exprsz(opstr);
            exprsz.append(string("sz"));
            z3::expr exprszsym = instantiateType("Numeric", context.constant(exprsz.c_str(), intSort));
            addConstraint(binopsym == Bit(exprszsym), "binbitop", ctx);
        }

        insertExpr(ctx, binopsym);
        return binopsym;
    }

    virtual antlrcpp::Any visitUnopexpr(BSVParser::UnopexprContext *ctx) override {
        //FIXME: Check for op
        BSVParser::ExprprimaryContext *ep = ctx->exprprimary();
        cerr << " visiting unop (" << ctx->getText() << " " << endl;

        z3::expr unopExpr = visit(ep);
        cerr << ") visit unop " << ctx->getText() << " " << unopExpr << " at " <<  sourceLocation(ctx) << endl;

        return unopExpr;
    }

    virtual antlrcpp::Any visitBitconcat(BSVParser::BitconcatContext *ctx) override {
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

    virtual antlrcpp::Any visitVarexpr(BSVParser::VarexprContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        cerr << "        Visiting var expr " << ctx->getText().c_str() << " " << ctx << endl;

        string varname(ctx->getText());
        shared_ptr<Declaration> varDecl = lexicalScope->lookup(varname);
        varDecls[ctx] = varDecl;

        if (varDecl) {
            cerr << "visiting var " << varname << " bindingType " << varDecl->bindingType << endl;
        }
        if (!varDecl || varDecl->bindingType == GlobalBindingType) {
            cerr << "visiting global var " << varname << " at " << sourceLocation(ctx) << endl;
            if (varDecl && varDecl->bsvtype) {
                varDecl->bsvtype->prettyPrint(cerr);
                cerr << endl;
                return bsvTypeToExpr(varDecl->bsvtype);
            }
        }

        string rhsname(varname + string("$rhs"));
        z3::expr varExpr = context.constant(context.str_symbol(varname.c_str()), typeSort);
        z3::expr rhsExpr = context.constant(context.str_symbol(rhsname.c_str()), typeSort);


        if (currentContext->enumtag.find(varname) != currentContext->enumtag.end()) {
            z3::expr var = context.constant(context.str_symbol(varname.c_str()), typeSort);
            vector<z3::expr> exprs;
            for (auto it = currentContext->enumtag.find(varname); it != currentContext->enumtag.end() && it->first == varname; ++it) {
                shared_ptr<Declaration> decl(it->second);
                fprintf(stderr, "Tag %s of type %s\n", varname.c_str(), decl->name.c_str());
                z3::func_decl type_decl = typeDecls.find(decl->name)->second;
                exprs.push_back(rhsExpr == type_decl());
            }

            addConstraint(orExprs(exprs), "enumtag", ctx);
        } else if (!varDecl || varDecl->bindingType == GlobalBindingType) {
            addConstraint(varExpr == rhsExpr, "varexpr", ctx);
        } else {
            // variable
            z3::func_decl reg_decl = typeDecls.find("Reg")->second;
            z3::expr regExpr = reg_decl(rhsExpr);
            addConstraint(varExpr == regExpr || varExpr == rhsExpr, "varexpr", ctx);
        }
        insertExpr(ctx, rhsExpr);
        cerr << "visit var expr " << ctx->getText() << " rhs expr " << rhsExpr << " ctx " << ctx << endl;
        return rhsExpr;
    }

    virtual antlrcpp::Any visitBlockexpr(BSVParser::BlockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStringliteral(BSVParser::StringliteralContext *ctx) override {
        return instantiateType("String");
    }

    virtual antlrcpp::Any visitIntliteral(BSVParser::IntliteralContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        fprintf(stderr, "        Visiting int literal %s\n", ctx->getText().c_str());
        z3::expr sym = context.constant(freshName("intlit"), typeSort);
        z3::expr widthExpr = context.constant(freshName("ilitsz"), intSort);

        addConstraint((sym == typeDecls.at("Integer")())
                      || (sym == instantiateType("Bit", instantiateType("Numeric", widthExpr))),
                      "intlit",
                      ctx);

        if (0) {
            solver.push();
            fprintf(stderr, "        check() %s\n", check_result_name[solver.check()]);
            solver.pop();
        }

        insertExpr(ctx, sym);
        return sym;
    }

    virtual antlrcpp::Any visitRealliteral(BSVParser::RealliteralContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCastexpr(BSVParser::CastexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeassertionexpr(BSVParser::TypeassertionexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitResetbyexpr(BSVParser::ResetbyexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUndefinedexpr(BSVParser::UndefinedexprContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        z3::expr undefined = freshConstant("_undefined_", typeSort);
        insertExpr(ctx, undefined);
        return undefined;
    }

    virtual antlrcpp::Any visitClockedbyexpr(BSVParser::ClockedbyexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFieldexpr(BSVParser::FieldexprContext *ctx) override {
        z3::expr exprtype = visit(ctx->exprprimary());
        string fieldname = ctx->field->getText();

        cerr << "Visit field expr " << fieldname << " exprtype " << exprtype << endl;

        z3::expr sym = context.constant(context.str_symbol(fieldname.c_str()), typeSort);

        vector<z3::expr> exprs;
        z3::expr fieldexpr = freshConstant(fieldname, typeSort);

        for (auto it = currentContext->memberDeclaration.find(fieldname);
             it != currentContext->memberDeclaration.end() && it->first == fieldname; ++it) {
            shared_ptr<Declaration> memberDecl(it->second);
            shared_ptr<Declaration> parentDecl(memberDecl->parent);
            cerr << "    field " << fieldname << " belongs to type " << parentDecl->name << endl;
            //FIXME continue here
            z3::func_decl type_decl = typeDecls.find(parentDecl->name)->second;
            z3::expr type_expr = freshConstant("_ph_", typeSort);
            switch (type_decl.arity()) {
                case 0: {
                    type_expr = type_decl();
                }
                    break;
                case 1: {
                    z3::expr type_var = freshConstant("_var_", typeSort);
                    type_expr = type_decl(type_var);
                }
                    break;
                default:
                    cerr << "Unhandled type arity " << type_decl;
            }
            shared_ptr<MethodDeclaration> methodDecl = memberDecl->methodDeclaration();
            shared_ptr<InterfaceDeclaration> interfaceDecl = parentDecl->interfaceDeclaration();
            if (interfaceDecl && methodDecl) {
                shared_ptr<BSVType> interfaceType = interfaceDecl->bsvtype;
                shared_ptr<BSVType> methodType = methodDecl->bsvtype;
                map<string,string> freshTypeVars;
                z3::expr interfaceExpr = bsvTypeToExpr(interfaceType, freshTypeVars);
                z3::expr methodExpr = bsvTypeToExpr(methodType, freshTypeVars);
                cerr << "convert method args to z3::expr ..." << endl;
                cerr << "    " << interfaceExpr << endl;
                cerr << "    " << methodExpr << endl;
                cerr << "    " << (exprtype == interfaceExpr && fieldexpr == methodExpr) << endl;
                exprs.push_back(exprtype == interfaceExpr && fieldexpr == methodExpr);
            } else {
                exprs.push_back(sym == type_expr);
            }
        }
        //z3::expr tracker(freshConstant("$track", boolSort));
        //insertTracker(ctx, tracker);
        if (exprs.size()) {
            addConstraint(orExprs(exprs), "fieldexpr", ctx);
            cerr << " returning fieldexpr " << fieldname << " exprs " << orExprs(exprs) << endl;
        }

        insertExpr(ctx, fieldexpr);
        return fieldexpr;
    }

    virtual antlrcpp::Any visitParenexpr(BSVParser::ParenexprContext *ctx) override {
        return visit(ctx->expression());
    }

    virtual antlrcpp::Any visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) override {
        z3::expr interfaceExpr = visit(ctx->bsvtype());
        for (int i = 0; ctx->interfacestmt(i); i++) {
            visit(ctx->interfacestmt(i));
        }
        return interfaceExpr;
    }

    virtual antlrcpp::Any visitCallexpr(BSVParser::CallexprContext *ctx) override {
        vector<BSVParser::ExpressionContext *> args = ctx->expression();
        cerr << "visit call expr " << ctx->getText() << (actionContext ? " side effect " : " constructor ") << " arity " << args.size() << endl;
        z3::expr fcn_expr = visit(ctx->fcn);
        z3::expr_vector arg_exprs(context);
        for (int i = 0; i < args.size(); i++) {
            //FIXME check parameters
            z3::expr arg_expr = visit(args[i]);
            arg_exprs.push_back(arg_expr);
        }
        string constructorName = "Function" + to_string(args.size() + 1);
        if (typeDecls.find(constructorName) == typeDecls.cend()) {
            cerr << "No constructor found for " << constructorName << endl;
        }
        z3::func_decl constructorDecl = typeDecls.find(constructorName)->second;
        z3::expr instance_expr = freshConstant((actionContext ? "rstT" : "mkinstance"), typeSort);
        arg_exprs.push_back(instance_expr);
        cerr << "instantiate " << constructorName << " arity " << arg_exprs.size()  << " constructor " << constructorDecl << endl;
        z3::expr result_expr = instantiateType(constructorDecl, arg_exprs);
        addConstraint(result_expr == fcn_expr, ctx->fcn->getText(), ctx);
        return instance_expr;
    }

    virtual antlrcpp::Any visitSyscallexpr(BSVParser::SyscallexprContext *ctx) override {
        //fixme visit parameters
        z3::func_decl voidDecl = typeDecls.find("Void")->second;
        return voidDecl();
    }

    virtual antlrcpp::Any visitValueofexpr(BSVParser::ValueofexprContext *ctx) override {
        return instantiateType("Integer");
    }

    virtual antlrcpp::Any visitTaggedunionexpr(BSVParser::TaggedunionexprContext *ctx) override {
        string tagname = ctx->tag->getText();

        string exprname(tagname + string("$expr"));
        z3::expr exprsym = context.constant(context.str_symbol(exprname.c_str()), typeSort);

        vector<z3::expr> exprs;
        for (auto it = currentContext->enumtag.find(tagname); it != currentContext->enumtag.end() && it->first == tagname; ++it) {
            shared_ptr<Declaration> decl(it->second);
            bool foundDecl = typeDecls.find(decl->name) != typeDecls.cend();
            cerr << "Tag exprprimary " << tagname << " of type " << decl->name << (foundDecl ? " found" : " not found") << endl;
            if (foundDecl) {
                z3::func_decl type_decl = typeDecls.find(decl->name)->second;
                exprs.push_back(exprsym == type_decl());
            }
        }
        if (exprs.size())
            addConstraint(orExprs(exprs), "tunionexpr", ctx);
        else
            cerr << "No enum definitions for expr " << ctx->getText() << endl;
        return exprsym;
    }

    virtual antlrcpp::Any visitArraysub(BSVParser::ArraysubContext *ctx) override {
        z3::expr arrayExpr = visit(ctx->array);
        z3::expr msbExpr = visit(ctx->msb);
        if (ctx->lsb) {
            z3::expr lsbExpr = visit(ctx->lsb);
        }
        cerr << "Fixme: array sub " << ctx->getText() << " z3 " << arrayExpr << endl;
        return arrayExpr;
    }

    virtual antlrcpp::Any visitMemberbinds(BSVParser::MemberbindsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMemberbind(BSVParser::MemberbindContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfacestmt(BSVParser::InterfacestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBeginendblock(BSVParser::BeginendblockContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRegwrite(BSVParser::RegwriteContext *ctx) override {
        z3::expr rhsExpr = visit(ctx->rhs);
        z3::expr lhsExpr = visit(ctx->lhs);
        z3::func_decl reg_decl = typeDecls.find("Reg")->second;
        z3::expr regExpr = reg_decl(rhsExpr);
        string tracker(freshString("regwrite"));
        addConstraint(lhsExpr == regExpr, "regwrite", ctx);
        cerr << "visit regwrite << " << (lhsExpr == regExpr) << endl;
        return lhsExpr;
    }

    virtual antlrcpp::Any visitStmt(BSVParser::StmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIfstmt(BSVParser::IfstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmt(BSVParser::CasestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmtdefaultitem(BSVParser::CasestmtdefaultitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitWhilestmt(BSVParser::WhilestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForstmt(BSVParser::ForstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForinit(BSVParser::ForinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSimplevardeclassign(BSVParser::SimplevardeclassignContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFortest(BSVParser::FortestContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForincr(BSVParser::ForincrContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarincr(BSVParser::VarincrContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPattern(BSVParser::PatternContext *ctx) override {
        if (ctx->var != NULL) {
            fprintf(stderr, "Visit pattern var %s\n", ctx->var->getText().c_str());
            return constant(ctx->var->getText().c_str(), typeSort);
        } else if (ctx->constantpattern() != NULL) {
            return visit(ctx->constantpattern());
        } else {
            fprintf(stderr, "Visit pattern wildcarrd %s\n", ctx->getText().c_str());
            return freshConstant("wildcard", typeSort);
        }
    }

    virtual antlrcpp::Any visitConstantpattern(BSVParser::ConstantpatternContext *ctx) override {
        //FIXME
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTaggedunionpattern(BSVParser::TaggedunionpatternContext *ctx) override {
        if (ctx->upperCaseIdentifier() != NULL) {
            string tagname(ctx->upperCaseIdentifier()->getText());
            fprintf(stderr, "Visit pattern tag %s\n", tagname.c_str());

            string patname(tagname + string("pat"));
            z3::expr patsym = context.constant(context.str_symbol(patname.c_str()), typeSort);

            vector<z3::expr> exprs;
            for (auto it = currentContext->enumtag.find(tagname); it != currentContext->enumtag.end() && it->first == tagname; ++it) {
                shared_ptr<Declaration> decl(it->second);
                fprintf(stderr, "Tag pattern %s of type %s\n", tagname.c_str(), decl->name.c_str());
                z3::func_decl type_decl = typeDecls.find(decl->name)->second;
                exprs.push_back(patsym == type_decl());
            }

            addConstraint(orExprs(exprs), "tunionpat", ctx);

            z3::expr patexpr = constant(patname, typeSort);
            insertExpr(ctx, patexpr);
            return patexpr;
        }
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTuplepattern(BSVParser::TuplepatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitProvisos(BSVParser::ProvisosContext *ctx) override {
        return nullptr;
    }

    virtual antlrcpp::Any visitProviso(BSVParser::ProvisoContext *ctx) override {
        return nullptr;
    }

    virtual antlrcpp::Any visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) override {
        return nullptr;
    }

    virtual antlrcpp::Any visitAttrspec(BSVParser::AttrspecContext *ctx) override {
        return nullptr;
    }

    shared_ptr<BSVType> bsvtype(z3::expr v, z3::model mod) {
        //cerr << "    " << v << " isint: " << v.is_int() << endl;
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
                    //cerr << recognizer.name() << " testing {" << jt->first << "} -> {" << recognizer(v) << "} " << is << endl;
                    break;
                }
            } catch (z3::exception e) {
                cerr << "z3::exception " << e << endl;
            }
            n++;
        }
        if (v.is_const()) {
            std::shared_ptr<BSVType> bsvt(new BSVType(name));
            //cerr << " const type ";
            //bsvt->prettyPrint(cerr);
            //cerr << endl;
            return bsvt;
        }
        std::shared_ptr<BSVType> bsvt(new BSVType(name));
        if (v.is_app()) {
            z3::func_decl func_decl = v.decl();
            size_t num_args = v.num_args();
            for (size_t i = 0; i < num_args; i++)
                bsvt->params.push_back(bsvtype(v.arg(i), mod));
        }
        //cerr << " app type: ";
        //bsvt->prettyPrint(cerr);
        //cerr << endl;
        return bsvt;
    }

public:
    static shared_ptr<BSVType> bsvtype(BSVParser::BsvtypeContext *ctx) {
        if (ctx->typeide() != NULL) {
            BSVParser::TypeideContext *typeide = ctx->typeide();
            if (typeide->typevar) {
                string varname = typeide->typevar->getText();

                //FIXME: could be numeric
                return make_shared<BSVType>(varname, BSVType_Symbolic, true);
            }

            vector<shared_ptr<BSVType>> param_types;
            vector<BSVParser::BsvtypeContext *> params = ctx->bsvtype();
            for (int i = 0; i < params.size(); i++) {
                param_types.push_back(bsvtype(params[i]));
            }
            string interfacename(typeide->name->getText());
            return make_shared<BSVType>(interfacename, param_types);
        } else if (ctx->var != NULL) {
            //FIXME: could be numeric
            return make_shared<BSVType>(ctx->getText(), BSVType_Symbolic, true);
        } else if (ctx->typenat() != NULL) {
            return make_shared<BSVType>(ctx->getText(), BSVType_Numeric, false);
        } else if (ctx->bsvtype(0) != NULL) {
            // parenthesized bsvtype expr
            return bsvtype(ctx->bsvtype(0));
        } else {
            cerr << "Unhandled bsvtype: " << ctx->getText() << endl;
            return make_shared<BSVType>("Unhandled");
        }
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::TypeformalContext *ctx) {
        return BSVType::create(ctx->typeide()->getText(),
                               (ctx->numeric != NULL ? BSVType_Numeric : BSVType_Symbolic),
                               true);
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::TypedeftypeContext *ctx) {
        BSVParser::TypeideContext *typeide = ctx->typeide();
        string name(typeide->name != 0 ? typeide->name->getText() : typeide->typevar->getText());
        vector<shared_ptr<BSVType>> params;
        if (ctx->typeformals() != 0) {
            vector<BSVParser::TypeformalContext *> formals = ctx->typeformals()->typeformal();
            for (int i = 0; i < formals.size(); i++)
                params.push_back(bsvtype(formals[i]));
        }
        return BSVType::create(name, params);
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::MethodprotoformalContext *ctx) {
        if (ctx->bsvtype()) {
            return bsvtype(ctx->bsvtype());
        } else {
            cerr << "unhandled: need to fill in the type from somewhere " << ctx->getText() << endl;
            return BSVType::create("Unspecified");
        }
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::MethodprotoContext *ctx) {
        shared_ptr<BSVType> returnType = bsvtype(ctx->bsvtype());
        vector<shared_ptr<BSVType>> params;
        if (ctx->methodprotoformals()) {
            vector<BSVParser::MethodprotoformalContext *> mpfs = ctx->methodprotoformals()->methodprotoformal();
            for (int i = 0; i < mpfs.size(); i++) {
                params.push_back(bsvtype(mpfs[i]));
            }
        }
        params.push_back(returnType);
        string function = "Function" + to_string(params.size());
        shared_ptr<BSVType> functionType = BSVType::create(function, params);
        cerr << "parsed methodproto type: " << ctx->getText() << endl;
        functionType->prettyPrint(cerr);
        cerr << endl;
        return functionType;
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::MethodformalContext *ctx) {
        if (ctx->bsvtype()) {
            return bsvtype(ctx->bsvtype());
        } else {
            cerr << "unhandled: need to fill in the type from somewhere " << ctx->getText() << endl;
            return BSVType::create("Unspecified");
        }
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::MethoddefContext *ctx) {
        if (ctx->bsvtype() == nullptr) {
            cerr << "No return type for method " << ctx->name->getText() << " at " << sourceLocation(ctx);
            return make_shared<BSVType>();
        }
        shared_ptr<BSVType> returnType = bsvtype(ctx->bsvtype());
        vector<shared_ptr<BSVType>> params;
        if (ctx->methodformals() != NULL) {
            vector<BSVParser::MethodformalContext *> mpfs = ctx->methodformals()->methodformal();
            for (int i = 0; i < mpfs.size(); i++) {
                params.push_back(bsvtype(mpfs[i]));
            }
        }
        params.push_back(returnType);
        string function = "Function" + to_string(params.size());
        shared_ptr<BSVType> functionType = BSVType::create(function, params);
        cerr << "parsed methodformal type: " << ctx->getText() << endl;
        functionType->prettyPrint(cerr);
        cerr << endl;
        return functionType;

    }

    static shared_ptr<BSVType> bsvtype(BSVParser::ModuleprotoContext *ctx) {
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

    static shared_ptr<BSVType> bsvtype(BSVParser::ModuleprotoformalContext *ctx) {
        return bsvtype(ctx->bsvtype());
    }

    static string sourceLocation(antlr4::ParserRuleContext *pContext);

    z3::expr instantiateType(z3::func_decl type_decl, const z3::expr_vector &params) {
        if (type_decl.arity() != params.size())
            cerr << "Unhandled type arity " << params.size() << " for type " << type_decl << endl;

        return type_decl(params);
    }

    z3::expr instantiateType(const string &type_name, const z3::expr_vector &params) {
        if (typeDecls.find(type_name) == typeDecls.cend()) {
            cerr << "No type constructor for " << type_name << endl;
        }
        z3::func_decl type_decl = typeDecls.find(type_name)->second;
        if (type_decl.arity() != params.size())
            cerr << "Unhandled type arity " << params.size() << " for type " << type_decl << endl;

        return type_decl(params);
    }

    z3::expr instantiateType(const string &type_name) {
        z3::expr_vector params(context);
        return instantiateType(type_name, params);
    }

    z3::expr instantiateType(const string &type_name, const z3::expr &param0) {
        z3::expr_vector params(context);
        params.push_back(param0);
        return instantiateType(type_name, params);
    }

    z3::expr instantiateType(const string &type_name, const z3::expr &param0, const z3::expr &param1) {
        z3::expr_vector params(context);
        params.push_back(param0);
        params.push_back(param1);
        return instantiateType(type_name, params);
    }

    z3::expr bsvTypeToExpr(shared_ptr<BSVType> bsvtype, map<string,string> &varmapping) {
        if (bsvtype->isVar) {
            string bsvname = bsvtype->name;
            string exprName;
            if (varmapping.find(bsvname) != varmapping.cend()) {
                exprName = varmapping.find(bsvname)->second;
            } else {
                exprName = freshString(bsvname);
                varmapping[bsvname] = exprName;
            }
            return constant(exprName, typeSort);
        } else if (bsvtype->isNumeric()) {
            return instantiateType("Numeric", context.int_val((int) strtol(bsvtype->name.c_str(), NULL, 0)));
        } else {
            z3::expr_vector arg_exprs(context);
            for (int i = 0; i < bsvtype->params.size(); i++) {
                arg_exprs.push_back(bsvTypeToExpr(bsvtype->params[i], varmapping));
            }
            cerr << " looking up type constructor for " << bsvtype->name << endl;
            z3::func_decl typeDecl = typeDecls.find(bsvtype->name)->second;
            return instantiateType(typeDecl, arg_exprs);
        }
    }

    z3::expr bsvTypeToExpr(shared_ptr<BSVType> bsvtype) {
        map<string,string> varmapping;
        return bsvTypeToExpr(bsvtype, varmapping);
    }
};
