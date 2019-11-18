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

using namespace std;

/**
 * Static analyzer of BSV package
 */
class TypeChecker : public BSVBaseVisitor {
    z3::context context;
    z3::solver solver;
    map<antlr4::ParserRuleContext *, z3::expr> exprs;
    map<antlr4::ParserRuleContext *, z3::expr> trackers;
    map<antlr4::ParserRuleContext *, shared_ptr<BSVType>> exprTypes;
    map<string, z3::func_decl> typeDecls;
    map<string, z3::func_decl> typeRecognizers;
    z3::sort typeSort, intSort, boolSort;

    map<string, bool> boolops;
    vector<shared_ptr<Declaration> > declarationList;
    vector<shared_ptr<Declaration> > typeDeclarationList;
    map<string, shared_ptr<Declaration> > declaration;
    map<string, shared_ptr<Declaration> > typeDeclaration;
    multimap<string, shared_ptr<Declaration> > enumtag;
    multimap<string, shared_ptr<Declaration> > memberDeclaration;

    vector<shared_ptr<Declaration> > subdeclaration;
    shared_ptr<Declaration> parentDecl;
    int nameCount;
public:
    TypeChecker()
            : context(), solver(context), typeSort(context), intSort(context), boolSort(context), nameCount(100) {
    }

    shared_ptr<BSVType> lookup(antlr4::ParserRuleContext *ctx) {
        if (exprTypes.find(ctx) != exprTypes.cend())
            return exprTypes.find(ctx)->second;
        return BSVType::create("FIXME");
    }

private:
    static const char *check_result_name[];

    void setupZ3Context();

    z3::symbol freshName(string name);

    z3::expr freshConstant(string name, z3::sort sort);

    z3::expr constant(string name, z3::sort sort);

    void insertExpr(antlr4::ParserRuleContext *ctx, z3::expr expr);

    void insertTracker(antlr4::ParserRuleContext *ctx, z3::expr tracker);

    z3::expr orExprs(vector<z3::expr> exprs);

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
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitPackagestmt(BSVParser::PackagestmtContext *ctx) override {
        setupZ3Context();
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackageide(BSVParser::PackageideContext *ctx) override {
        assert(0);
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitInterfacedecl(BSVParser::InterfacedeclContext *ctx) override {
        BSVParser::TypedeftypeContext *typedeftype = ctx->typedeftype();
        string name(typedeftype->getText());
        shared_ptr<BSVType> bsvtype(new BSVType(name));
        shared_ptr<InterfaceDeclaration> decl(new InterfaceDeclaration(name, bsvtype));
        typeDeclarationList.push_back(decl);
        typeDeclaration[name] = decl;
        cerr << "unhandled visitInterfacedecl: " << name << endl;

        auto members = ctx->interfacememberdecl();
        for (int i = 0; i < members.size(); i++) {
            shared_ptr<Declaration> memberDecl((Declaration *)visitInterfacememberdecl(members[i]));

            cerr << " subinterface decl " << memberDecl->name << endl;
            memberDeclaration.emplace(memberDecl->name, decl);
            decl->members.push_back(memberDecl);
        }
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) override {
        cerr << "visitInterfacememberdecl: " << ctx->getText() << endl;
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodproto(BSVParser::MethodprotoContext *ctx) override {
        fprintf(stderr, "Visit method proto %s\n", ctx->getText().c_str());
        shared_ptr<BSVType> methodType = bsvtype(ctx);
        return (Declaration *)new MethodDeclaration(ctx->name->getText(), methodType);
    }

    virtual antlrcpp::Any visitMethodprotoformals(BSVParser::MethodprotoformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodprotoformal(BSVParser::MethodprotoformalContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubinterfacedecl(BSVParser::SubinterfacedeclContext *ctx) override {
        return visitChildren(ctx);
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefenum(BSVParser::TypedefenumContext *ctx) override {
        BSVParser::UpperCaseIdentifierContext *id = ctx->upperCaseIdentifier();
        string name(id->getText());
        shared_ptr<BSVType> bsvtype(new BSVType(name));
        shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
        parentDecl = decl;
        typeDeclarationList.push_back(decl);
        typeDeclaration[name] = decl;
        subdeclaration.clear();

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
        enumtag.insert(make_pair(name, parentDecl));
        return decl;
    }

    virtual antlrcpp::Any visitTypedefstruct(BSVParser::TypedefstructContext *ctx) override {
        BSVParser::TypedeftypeContext *typedeftype = ctx->typedeftype();
        string name(typedeftype->getText());
        shared_ptr<BSVType> bsvtype(new BSVType(name));
        shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
        typeDeclarationList.push_back(decl);
        typeDeclaration[name] = decl;
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
        vector<BSVParser::VarinitContext *> varinits = ctx->varinit();
        for (size_t i = 0; i < varinits.size(); i++) {
            BSVParser::VarinitContext *varinit = varinits[i];
            z3::expr lhsexpr = visit(varinit->var);
            if (ctx->t) {
                z3::expr bsvtypeExpr = visit(ctx->t);
                solver.add(lhsexpr == bsvtypeExpr);
            }
            cerr << "visit VarInit rhs " << varinit->rhs->getText() << endl;
            z3::expr rhsexpr = visit(varinit->rhs);
            solver.add(lhsexpr == rhsexpr);
        }
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionbinding(BSVParser::ActionbindingContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        fprintf(stderr, "        Visiting action binding %s\n", ctx->getText().c_str());

        string varname(ctx->var->getText().c_str());
        z3::expr typesym = visit(ctx->t);
        z3::expr varsym = context.constant(context.str_symbol(varname.c_str()), typeSort);
        string rhsname(varname + string("$rhs"));
        z3::expr rhstype = context.constant(rhsname.c_str(), typeSort);
        z3::func_decl reg_decl = typeDecls.find("Reg")->second;


        solver.add(typesym == varsym);
        solver.add((varsym == rhstype) || (varsym == reg_decl(rhstype)));

        // handle reg dereference here ?

        insertExpr(ctx, varsym);
        return varsym;
    }

    virtual antlrcpp::Any visitPatternbinding(BSVParser::PatternbindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuledef(BSVParser::ModuledefContext *ctx) override {
        setupZ3Context();

        string module_name = ctx->moduleproto()->name->getText();
        fprintf(stderr, "tc ModuleDef %s\n", module_name.c_str());
        solver.push();
        antlrcpp::Any result = visitChildren(ctx);
        z3::check_result checked = solver.check();
        fprintf(stderr, "  Type checking module %s: %s\n", module_name.c_str(), check_result_name[checked]);
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
            for (auto it = trackers.cbegin(); it != trackers.cend(); ++it) {
                z3::expr e = it->second;
                try {
                    z3::expr v = mod.eval(e, true);
                    cerr << e << " evaluates to " << v << endl;
                } catch (const exception &e) {
                    cerr << "exception" << endl;
                }
            }
        }
        solver.pop();
        return result;
    }

    virtual antlrcpp::Any visitModuleproto(BSVParser::ModuleprotoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModulestmt(BSVParser::ModulestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleinst(BSVParser::ModuleinstContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethoddef(BSVParser::MethoddefContext *ctx) override {
        fprintf(stderr, "    tc MethodDef %s\n", ctx->name->getText().c_str());
        shared_ptr<BSVType> methodType = bsvtype(ctx);
        if (ctx->methodcond() != NULL) {
            z3::expr condtype = visit(ctx->methodcond());
        }
        return new MethodDefinition(ctx->name->getText(), methodType);
    }

    virtual antlrcpp::Any visitMethodformals(BSVParser::MethodformalsContext *ctx) override {
        assert(0);
        return 0;
    }

    virtual antlrcpp::Any visitMethodformal(BSVParser::MethodformalContext *ctx) override {
        assert(0);
        return 0;
    }

    virtual antlrcpp::Any visitMethodcond(BSVParser::MethodcondContext *ctx) override {
        z3::expr condtype = visit(ctx->expression());
        z3::func_decl boolcon = typeDecls.find("Bool")->second;
        solver.add(condtype == boolcon());
        return condtype;
    }

    virtual antlrcpp::Any visitSubinterfacedef(BSVParser::SubinterfacedefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRuledef(BSVParser::RuledefContext *ctx) override {
        fprintf(stderr, "    tc RuleDef %s\n", ctx->name->getText().c_str());
        if (ctx->rulecond() != NULL) {
            z3::expr condtype = visit(ctx->rulecond());
        }

        for (int i = 0; i < ctx->stmt().size(); i++) {
            visit(ctx->stmt().at(i));
        }

        return freshConstant("rule", typeSort);
    }

    virtual antlrcpp::Any visitRulecond(BSVParser::RulecondContext *ctx) override {
        z3::expr condtype = visit(ctx->expression());
        z3::func_decl boolcon = typeDecls.find("Bool")->second;
        solver.add(condtype == boolcon());
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLvalue(BSVParser::LvalueContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBsvtype(BSVParser::BsvtypeContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        fprintf(stderr, "        Visiting bsvtype %s\n", ctx->getText().c_str());

        z3::expr bsvtype(context);

        if (ctx->typeide() != NULL) {
            BSVParser::TypeideContext *typeide = ctx->typeide();

            if (typeide != NULL) {
                string name = (typeide->name != NULL) ? typeide->name->getText() : typeide->typevar->getText();
                auto jt = typeDecls.find(name);
                if (jt != typeDecls.end()) {
                    z3::func_decl decl = jt->second;
                    vector<BSVParser::BsvtypeContext *> typeArgs = ctx->bsvtype();
                    int numArgs = typeArgs.size();
                    switch (numArgs) {
                        case 0:
                            bsvtype = decl();
                            break;
                        case 1: {
                            z3::expr t0 = visit(typeArgs[0]);
                            bsvtype = decl(t0);
                        }
                            break;
                        case 2: {
                            z3::expr t0 = visit(typeArgs[0]);
                            z3::expr t1 = visit(typeArgs[1]);
                            bsvtype = decl(t0, t1);
                        }
                            break;
                        default:
                            fprintf(stderr, "Too many type arguments: %d\n", numArgs);
                    }
                } else {
                    cerr << "unhandled bsvtype not in typeDecls " << ctx->getText() << endl;
                    z3::func_decl bozoDecl = typeDecls.find("Bozo")->second;
                    bsvtype = bozoDecl();
                }
            }
        } else if (ctx->typenat() != NULL) {
            return context.int_val((int) strtol(ctx->getText().c_str(), NULL, 0));
        } else {
            fprintf(stderr, "Unhandled bsvtype %s\n", ctx->getText().c_str());
        }

        solver.push();
        fprintf(stderr, "        check(%s) %s\n", ctx->getText().c_str(), check_result_name[solver.check()]);
        solver.pop();

        insertExpr(ctx, bsvtype);
        return bsvtype;
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
                    solver.add(exprtype == itemtype);
                }
                z3::expr bodytype = visit(item->body);
                solver.add(casetype == bodytype);
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

        solver.add(leftsym == rightsym);
        solver.push();
        fprintf(stderr, "        check(%s) %s\n", ctx->getText().c_str(), check_result_name[solver.check()]);
        solver.pop();


        string opstr(ctx->op->getText());
        char opnamebuf[128];
        snprintf(opnamebuf, sizeof(opnamebuf) - 1, "expr%s-%d", opstr.c_str(), nameCount++);
        string binopstr(opnamebuf);
        z3::expr binopsym = context.constant(binopstr.c_str(), typeSort);
        if (boolops.find(opstr) != boolops.end()) {
            fprintf(stderr, "Bool expr %s\n", ctx->getText().c_str());
            z3::func_decl Bool = typeDecls.find("Bool")->second;
            solver.add(binopsym == Bool());
        } else {
            fprintf(stderr, "Bit expr %s\n", ctx->getText().c_str());
            z3::func_decl Bit = typeDecls.find("Bit")->second;
            string exprsz(opstr);
            exprsz.append(string("sz"));
            z3::expr exprszsym = context.constant(exprsz.c_str(), intSort);
            solver.add(binopsym == Bit(exprszsym));
        }

        insertExpr(ctx, binopsym);
        return binopsym;
    }

    virtual antlrcpp::Any visitUnopexpr(BSVParser::UnopexprContext *ctx) override {
        fprintf(stderr, "        Visit unop %s\n", ctx->getText().c_str());
        BSVParser::ExprprimaryContext *ep = ctx->exprprimary();
        return visit(ep);
    }

    virtual antlrcpp::Any visitBitconcat(BSVParser::BitconcatContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarexpr(BSVParser::VarexprContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        fprintf(stderr, "        Visiting var expr %s\n", ctx->getText().c_str());

        string varname(ctx->getText());
        string rhsname(varname + string("$rhs"));
        z3::expr sym = context.constant(context.str_symbol(rhsname.c_str()), typeSort);
        if (enumtag.find(varname) != enumtag.end()) {
            z3::expr var = context.constant(context.str_symbol(varname.c_str()), typeSort);
            vector<z3::expr> exprs;
            for (auto it = enumtag.find(varname); it != enumtag.end() && it->first == varname; ++it) {
                shared_ptr<Declaration> decl(it->second);
                fprintf(stderr, "Tag %s of type %s\n", varname.c_str(), decl->name.c_str());
                z3::func_decl type_decl = typeDecls.find(decl->name)->second;
                exprs.push_back(sym == type_decl());
            }
            z3::expr tracker(freshConstant("$track", boolSort));
            insertTracker(ctx, tracker);

            solver.add(orExprs(exprs), tracker);
        }
        insertExpr(ctx, sym);
        return sym;
    }

    virtual antlrcpp::Any visitBlockexpr(BSVParser::BlockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStringliteral(BSVParser::StringliteralContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIntliteral(BSVParser::IntliteralContext *ctx) override {
        auto it = exprs.find(ctx);
        if (it != exprs.end())
            return it->second;
        fprintf(stderr, "        Visiting int literal %s\n", ctx->getText().c_str());
        z3::expr sym = context.constant(freshName("intlit"), typeSort);
        z3::expr width = context.constant(freshName("ilitsz"), intSort);

        solver.add((sym == typeDecls.at("Integer")())
                   || (sym == typeDecls.at("Bit")(width)));

        solver.push();
        fprintf(stderr, "        check() %s\n", check_result_name[solver.check()]);
        solver.pop();

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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitClockedbyexpr(BSVParser::ClockedbyexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFieldexpr(BSVParser::FieldexprContext *ctx) override {
        z3::expr exprtype = visit(ctx->exprprimary());
        string fieldname = ctx->field->getText();

        cerr << "Visit field expr " << fieldname << endl;

        z3::expr sym = context.constant(context.str_symbol(fieldname.c_str()), typeSort);

        vector<z3::expr> exprs;

        for (auto it = memberDeclaration.find(fieldname); it != memberDeclaration.end() && it->first == fieldname; ++it) {
            shared_ptr<Declaration> decl(it->second);
            cerr << "    " << fieldname << " belongs to type " << decl->name << endl;
            //FIXME continue here
            z3::func_decl type_decl = typeDecls.find(decl->name)->second;
            exprs.push_back(sym == type_decl());
        }
        z3::expr tracker(freshConstant("$track", boolSort));
        insertTracker(ctx, tracker);

        solver.add(orExprs(exprs), tracker);

        z3::expr fieldexpr = constant(fieldname, typeSort);
        insertExpr(ctx, fieldexpr);
        cerr << " returning fieldexpr " << endl;
        return fieldexpr;
    }

    virtual antlrcpp::Any visitParenexpr(BSVParser::ParenexprContext *ctx) override {
        return visit(ctx->expression());
    }

    virtual antlrcpp::Any visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCallexpr(BSVParser::CallexprContext *ctx) override {
        //fixme parameters
        return visit(ctx->fcn);
    }

    virtual antlrcpp::Any visitValueofexpr(BSVParser::ValueofexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTaggedunionexpr(BSVParser::TaggedunionexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitArraysub(BSVParser::ArraysubContext *ctx) override {
        return visitChildren(ctx);
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
        return visitChildren(ctx);
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
            for (auto it = enumtag.find(tagname); it != enumtag.end() && it->first == tagname; ++it) {
                shared_ptr<Declaration> decl(it->second);
                fprintf(stderr, "Tag pattern %s of type %s\n", tagname.c_str(), decl->name.c_str());
                z3::func_decl type_decl = typeDecls.find(decl->name)->second;
                exprs.push_back(patsym == type_decl());
            }
            z3::expr tracker(freshConstant("$track", boolSort));
            insertTracker(ctx, tracker);

            solver.add(orExprs(exprs), tracker);

            z3::expr patexpr = constant(patname, typeSort);
            insertExpr(ctx, patexpr);
            return patexpr;
        }
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTuplepattern(BSVParser::TuplepatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitAttrspec(BSVParser::AttrspecContext *ctx) override {
        return visitChildren(ctx);
    }

    shared_ptr<BSVType> bsvtype(z3::expr v, z3::model mod) {
        //cerr << "    " << v << " isint: " << v.is_int() << endl;
        if (v.is_int())
            return BSVType::create(v.to_string(), BSVType_Numeric, false);

        z3::sort v_sort = v.get_sort();
        Z3_sort z3_sort = (Z3_sort)v_sort;
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
            vector<shared_ptr<BSVType>> param_types;
            vector<BSVParser::BsvtypeContext *> params = ctx->bsvtype();
            for (int i = 0; i < params.size(); i++) {
                param_types.push_back(bsvtype(params[i]));
            }
            BSVParser::TypeideContext *typeide = ctx->typeide();
            string name(typeide->name != NULL ? typeide->name->getText() : typeide->typevar->getText());
            return BSVType::create(name, param_types);
        } else if (ctx->var != NULL) {
            //FIXME: could be numeric
            return BSVType::create(ctx->getText(), BSVType_Symbolic, true);
        } else if (ctx->typenat() != NULL) {
            return BSVType::create(ctx->getText(), BSVType_Numeric, false);
        } else if (ctx->bsvtype(0) != NULL) {
            // parenthesized bsvtype expr
            return bsvtype(ctx->bsvtype(0));
        } else {
            cerr << "Unhandled bsvtype: " << ctx->getText() << endl;
            return BSVType::create("Unhandled");
        }
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::TypeformalContext *ctx) {
        return BSVType::create(ctx->typeide()->getText(),
                               (ctx->numeric != NULL? BSVType_Numeric : BSVType_Symbolic),
                               true);
    }

    static shared_ptr<BSVType> bsvtype(BSVParser::TypedeftypeContext *ctx) {
        BSVParser::TypeideContext *typeide = ctx->typeide();
        string name(typeide->name != 0 ? typeide->name->getText() : typeide->typevar->getText());
        vector<shared_ptr<BSVType>> params;
        if (ctx->typeformals() != 0) {
            vector<BSVParser::TypeformalContext*> formals = ctx->typeformals()->typeformal();
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
        if (ctx->methodprotoformals() != NULL) {
            shared_ptr<BSVType> functionType = returnType;
            vector<BSVParser::MethodprotoformalContext *> mpfs = ctx->methodprotoformals()->methodprotoformal();
            for (int i = 0; i < mpfs.size(); i++) {
                vector<shared_ptr<BSVType>> params;
                params.push_back(bsvtype(mpfs[i]));
                params.push_back(functionType);
                functionType = BSVType::create("Function", params);
            }
            cerr << "parsed methodproto type: " << ctx->getText() << endl;
            functionType->prettyPrint(cerr);
            cerr << endl;
            return functionType;
        } else {
            //FIXME: Action methods
            return returnType;
        }
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
        shared_ptr<BSVType> returnType = bsvtype(ctx->bsvtype());
        if (ctx->methodformals() != NULL) {
            shared_ptr<BSVType> functionType = returnType;
            vector<BSVParser::MethodformalContext *> mpfs = ctx->methodformals()->methodformal();
            for (int i = 0; i < mpfs.size(); i++) {
                vector<shared_ptr<BSVType>> params;
                params.push_back(bsvtype(mpfs[i]));
                params.push_back(functionType);
                functionType = BSVType::create("Function", params);
            }
            cerr << "parsed methodformal type: " << ctx->getText() << endl;
            functionType->prettyPrint(cerr);
            cerr << endl;
            return functionType;
        } else {
            //FIXME: Action methods
            return returnType;
        }
    }

};