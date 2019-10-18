#pragma once

#include <assert.h>

#include <map>
#include <iostream>
#include "antlr4-runtime.h"
#include "z3++.h"
#include "z3.h"
#include "BSVBaseVisitor.h"
#include "Declaration.h"

/**
 * Static analyzer of BSV package
 */
class TypeChecker : public BSVBaseVisitor {
    z3::context context;
    z3::solver solver;
    std::map<antlr4::ParserRuleContext *, z3::expr> exprs;
    std::map<antlr4::ParserRuleContext *, z3::expr> trackers;
    std::map<std::string, z3::func_decl> typeDecls;
    z3::sort typeSort, intSort, boolSort;

    std::map<std::string, bool> boolops;
    std::vector<std::shared_ptr<Declaration> > declarationList;
    std::vector<std::shared_ptr<Declaration> > typeDeclarationList;
    std::map<std::string, std::shared_ptr<Declaration> > declaration;
    std::map<std::string, std::shared_ptr<Declaration> > typeDeclaration;
    std::multimap<std::string, std::shared_ptr<Declaration> > enumtag;
    std::vector<std::shared_ptr<Declaration> > subdeclaration;
    std::shared_ptr<Declaration> parentDecl;
    int nameCount;
public:
    TypeChecker()
            : context(), solver(context), typeSort(context), intSort(context), boolSort(context), nameCount(100) {
    }

private:
    static const char *check_result_name[];

    void setupZ3Context();

    z3::symbol freshName(std::string name);

    z3::expr freshConstant(std::string name, z3::sort sort);

    z3::expr constant(std::string name, z3::sort sort);

    void insertExpr(antlr4::ParserRuleContext *ctx, z3::expr expr);

    void insertTracker(antlr4::ParserRuleContext *ctx, z3::expr tracker);

    z3::expr orExprs(std::vector<z3::expr> exprs);

    std::shared_ptr<BSVType> exprToBSVType(z3::expr expr);

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
        std::string varname(ctx->getText());
        return context.constant(context.str_symbol(varname.c_str()), typeSort);
    }

    virtual antlrcpp::Any visitUpperCaseIdentifier(BSVParser::UpperCaseIdentifierContext *ctx) override {
        assert(0);
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitAnyidentifier(BSVParser::AnyidentifierContext *ctx) override {
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
        std::string name(typedeftype->getText());
        std::shared_ptr<BSVType> bsvtype(new BSVType(name));
        std::shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
        typeDeclarationList.push_back(decl);
        typeDeclaration[name] = decl;
        return freshConstant(__FUNCTION__, typeSort);
    }

    virtual antlrcpp::Any visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) override {
        if (ctx->methodproto()) {
        } else {
        }
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodproto(BSVParser::MethodprotoContext *ctx) override {
        fprintf(stderr, "Visit method proto %s\n", ctx->getText().c_str());
        return visitChildren(ctx);
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
        std::string name(id->getText());
        std::shared_ptr<BSVType> bsvtype(new BSVType(name));
        std::shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
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
        std::string name(tag->getText());
        std::shared_ptr<BSVType> bsvtype(new BSVType(name));
        std::shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
        //declarationList.push_back(decl);
        enumtag.insert(std::make_pair(name, parentDecl));
        return decl;
    }

    virtual antlrcpp::Any visitTypedefstruct(BSVParser::TypedefstructContext *ctx) override {
        BSVParser::TypedeftypeContext *typedeftype = ctx->typedeftype();
        std::string name(typedeftype->getText());
        std::shared_ptr<BSVType> bsvtype(new BSVType(name));
        std::shared_ptr<Declaration> decl(new Declaration(name, bsvtype));
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
        std::vector<BSVParser::VarinitContext *> varinits = ctx->varinit();
        for (size_t i = 0; i < varinits.size(); i++) {
            BSVParser::VarinitContext *varinit = varinits[i];
            z3::expr lhsexpr = visit(varinit->var);
            if (ctx->t) {
                z3::expr bsvtypeExpr = visit(ctx->t);
                solver.add(lhsexpr == bsvtypeExpr);
            }
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

        std::string varname(ctx->var->getText().c_str());
        z3::expr typesym = visit(ctx->t);
        z3::expr varsym = context.constant(context.str_symbol(varname.c_str()), typeSort);
        std::string rhsname(varname + std::string("$rhs"));
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

        std::string module_name = ctx->moduleproto()->name->getText();
        fprintf(stderr, "tc ModuleDef %s\n", module_name.c_str());
        solver.push();
        antlrcpp::Any result = visitChildren(ctx);
        z3::check_result checked = solver.check();
        fprintf(stderr, "  Type checking module %s: %s\n", module_name.c_str(), check_result_name[checked]);
        if (checked == z3::sat) {
            z3::model mod = solver.get_model();
            std::cerr << "model: " << mod << std::endl;
            std::cerr << exprs.size() << " exprs" << std::endl;
            for (auto it = exprs.cbegin(); it != exprs.cend(); ++it) {
                z3::expr e = it->second;
                try {
                    z3::expr v = mod.eval(e, true);
                    std::cerr << e << " evaluates to " << v << std::endl;
                } catch (const std::exception &e) {
                    std::cerr << "exception" << std::endl;
                }
            }
            for (auto it = trackers.cbegin(); it != trackers.cend(); ++it) {
                z3::expr e = it->second;
                try {
                    z3::expr v = mod.eval(e, true);
                    std::cerr << e << " evaluates to " << v << std::endl;
                } catch (const std::exception &e) {
                    std::cerr << "exception" << std::endl;
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
        if (ctx->methodcond() != NULL) {
            z3::expr condtype = visit(ctx->methodcond());
        }
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodformals(BSVParser::MethodformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodformal(BSVParser::MethodformalContext *ctx) override {
        return visitChildren(ctx);
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

            if (typeide->name != NULL) {
                std::string name = typeide->name->getText();
                auto jt = typeDecls.find(name);
                if (jt != typeDecls.end()) {
                    z3::func_decl decl = jt->second;
                    std::vector<BSVParser::BsvtypeContext *> typeArgs = ctx->bsvtype();
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


        std::string opstr(ctx->op->getText());
        char opnamebuf[128];
        snprintf(opnamebuf, sizeof(opnamebuf) - 1, "expr%s-%d", opstr.c_str(), nameCount++);
        std::string binopstr(opnamebuf);
        z3::expr binopsym = context.constant(binopstr.c_str(), typeSort);
        if (boolops.find(opstr) != boolops.end()) {
            fprintf(stderr, "Bool expr %s\n", ctx->getText().c_str());
            z3::func_decl Bool = typeDecls.find("Bool")->second;
            solver.add(binopsym == Bool());
        } else {
            fprintf(stderr, "Bit expr %s\n", ctx->getText().c_str());
            z3::func_decl Bit = typeDecls.find("Bit")->second;
            std::string exprsz(opstr);
            exprsz.append(std::string("sz"));
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

        std::string varname(ctx->getText());
        std::string rhsname(varname + std::string("$rhs"));
        z3::expr sym = context.constant(context.str_symbol(rhsname.c_str()), typeSort);
        if (enumtag.find(varname) != enumtag.end()) {
            z3::expr var = context.constant(context.str_symbol(varname.c_str()), typeSort);
            std::vector<z3::expr> exprs;
            for (auto it = enumtag.find(varname); it != enumtag.end() && it->first == varname; ++it) {
                std::shared_ptr<Declaration> decl(it->second);
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParenexpr(BSVParser::ParenexprContext *ctx) override {
        return visit(ctx->expression());
    }

    virtual antlrcpp::Any visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCallexpr(BSVParser::CallexprContext *ctx) override {
        return visitChildren(ctx);
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitConstantpattern(BSVParser::ConstantpatternContext *ctx) override {
        //FIXME
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTaggedunionpattern(BSVParser::TaggedunionpatternContext *ctx) override {
        if (ctx->upperCaseIdentifier() != NULL) {
            std::string tagname(ctx->upperCaseIdentifier()->getText());
            fprintf(stderr, "Visit pattern tag %s\n", tagname.c_str());

            std::string patname(tagname + std::string("pat"));
            z3::expr patsym = context.constant(context.str_symbol(patname.c_str()), typeSort);

            std::vector<z3::expr> exprs;
            for (auto it = enumtag.find(tagname); it != enumtag.end() && it->first == tagname; ++it) {
                std::shared_ptr<Declaration> decl(it->second);
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

};
