#pragma once

#include <map>
#include "antlr4-runtime.h"
#include "z3++.h"
#include "z3.h"
#include "BSVBaseVisitor.h"
#include <iostream>

const char *check_result_name[] = {
    "unsat", "sat", "unknown"
};

/**
 * Static analyzer of BSV package
 */
class  TypeChecker : public BSVBaseVisitor {
    z3::context context;
    z3::solver solver;
    std::map<antlr4::ParserRuleContext *, z3::expr> exprs;
    std::map<std::string, z3::func_decl> typeDecls;
    std::map<std::string, bool> boolops;
    z3::sort typeSort, intSort, boolSort;
    z3::func_decl action_decl, actionvalue_decl, bit_decl, bool_decl, bozo_decl, integer_decl, real_decl, reg_decl, rule_decl, string_decl, void_decl;
    int nameCount;
public:
    TypeChecker()
	: context(), solver(context)
	, typeSort(context), intSort(context), boolSort(context)
	, action_decl(context), actionvalue_decl(context), bit_decl(context), bool_decl(context), bozo_decl(context), integer_decl(context)
	, real_decl(context), reg_decl(context), rule_decl(context), string_decl(context), void_decl(context)
	, nameCount(100)
    {
	intSort = context.int_sort();
	boolSort = context.bool_sort();
	Z3_constructor action_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Action"), Z3_mk_string_symbol(context, "isAction"),
						      0, NULL, NULL, NULL);
	Z3_symbol actionvalue_field_names[] = { Z3_mk_string_symbol(context, "elt") };
	Z3_sort actionvalue_field_sorts[] = { NULL };
	unsigned actionvalue_field_sort_refs[] = { 0 };
	Z3_constructor actionvalue_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "ActionValue"), Z3_mk_string_symbol(context, "isActionValue"),
							   1,
							   actionvalue_field_names,
							   actionvalue_field_sorts,
							   actionvalue_field_sort_refs);
	Z3_symbol bit_field_names[] = { Z3_mk_string_symbol(context, "width") };
	Z3_sort bit_field_sorts[] = { intSort };
	unsigned bit_field_sort_refs[] = { 0 };
	Z3_constructor bit_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Bit"), Z3_mk_string_symbol(context, "isBit"),
						   1, 
						   bit_field_names,
						   bit_field_sorts,
						   bit_field_sort_refs);
	Z3_constructor bool_con = Z3_mk_constructor(context,
						    Z3_mk_string_symbol(context, "Bool"), Z3_mk_string_symbol(context, "isBool"),
						    0, NULL, NULL, NULL);
	Z3_constructor bozo_con = Z3_mk_constructor(context,
						    Z3_mk_string_symbol(context, "Bozo"), Z3_mk_string_symbol(context, "isBozo"),
						    0, NULL, NULL, NULL);
	Z3_constructor integer_con = Z3_mk_constructor(context,
						       Z3_mk_string_symbol(context, "Integer"), Z3_mk_string_symbol(context, "isInteger"),
						       0, NULL, NULL, NULL);
	Z3_constructor real_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Real"), Z3_mk_string_symbol(context, "isReal"),
						    0, NULL, NULL, NULL);
	Z3_symbol reg_field_names[] = { Z3_mk_string_symbol(context, "elt") };
	Z3_sort reg_field_sorts[] = { NULL };
	unsigned reg_field_sort_refs[] = { 0 };
	Z3_constructor reg_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Reg"), Z3_mk_string_symbol(context, "isReg"),
						   1,
						   reg_field_names,
						   reg_field_sorts,
						   reg_field_sort_refs );
	Z3_constructor rule_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Rule"), Z3_mk_string_symbol(context, "isRule"),
						    0, NULL, NULL, NULL);
	Z3_constructor string_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "String"), Z3_mk_string_symbol(context, "isString"),
						      0, NULL, NULL, NULL);
	Z3_constructor void_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Void"), Z3_mk_string_symbol(context, "isVoid"),
						    0, NULL, NULL, NULL);


	//FIXME: add support for user defined types
	Z3_constructor constructors[] = {
	    action_con, actionvalue_con, bit_con, bool_con, bozo_con,
	    integer_con, real_con, reg_con, rule_con, string_con, void_con
	};
	unsigned num_constructors = sizeof(constructors) / sizeof(constructors[0]);
	typeSort = z3::sort(context, Z3_mk_datatype(context, Z3_mk_string_symbol(context, "BSVType"),
						    num_constructors,
						    constructors));

	for (unsigned i = 0; i < num_constructors; i++) {
	    Z3_func_decl func_decl = Z3_get_datatype_sort_constructor(context, typeSort, i);
	    Z3_symbol name = Z3_get_decl_name(context, func_decl);
	    fprintf(stderr, "Constructor %d name is %s\n", i, Z3_get_symbol_string(context, name));
	    // since no default constructor for z3::func_decl, use insert with a pair
	    typeDecls.insert(std::pair<std::string, z3::func_decl>(Z3_get_symbol_string(context, name), z3::func_decl(context, func_decl)));
	}
	boolops["=="] =  true;
	boolops["!="] =  true;
	boolops["<"] =  true;
	boolops[">"] =  true;
	boolops["<="] =  true;
	boolops[">="] =  true;
	boolops["&&"] =  true;
	boolops["||"] =  true;
    }

    z3::symbol freshName(std::string name) {
	char uniq_name[128];
	snprintf(uniq_name, sizeof(uniq_name), "%s-%d", name.c_str(), nameCount++);
	return context.str_symbol(uniq_name);
    }

    void insertExpr(antlr4::ParserRuleContext *ctx, z3::expr expr) {
	fprintf(stderr, "  insert expr %s\n", ctx->getText().c_str());
	exprs.insert(std::pair<antlr4::ParserRuleContext *, z3::expr>(ctx, expr));
    }

    virtual antlrcpp::Any visitPackagedef(BSVParser::PackagedefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackagedecl(BSVParser::PackagedeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitEndpackage(BSVParser::EndpackageContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLowerCaseIdentifier(BSVParser::LowerCaseIdentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitUpperCaseIdentifier(BSVParser::UpperCaseIdentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIdentifier(BSVParser::IdentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitAnyidentifier(BSVParser::AnyidentifierContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExportdecl(BSVParser::ExportdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitExportitem(BSVParser::ExportitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitImportdecl(BSVParser::ImportdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitImportitem(BSVParser::ImportitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackagestmt(BSVParser::PackagestmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPackageide(BSVParser::PackageideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfacedecl(BSVParser::InterfacedeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfacememberdecl(BSVParser::InterfacememberdeclContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodproto(BSVParser::MethodprotoContext *ctx) override {
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

    virtual antlrcpp::Any visitTypedecl(BSVParser::TypedeclContext *ctx) override {
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefenumelement(BSVParser::TypedefenumelementContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypedefstruct(BSVParser::TypedefstructContext *ctx) override {
        return visitChildren(ctx);
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

    virtual antlrcpp::Any visitVarBinding(BSVParser::VarBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionBinding(BSVParser::ActionBindingContext *ctx) override {
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

    virtual antlrcpp::Any visitLetBinding(BSVParser::LetBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPatternBinding(BSVParser::PatternBindingContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitVarinit(BSVParser::VarinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitArraydims(BSVParser::ArraydimsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTypeclassdecl(BSVParser::TypeclassdeclContext *ctx) override {
        return visitChildren(ctx);
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitOverloadeddef(BSVParser::OverloadeddefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuledef(BSVParser::ModuledefContext *ctx) override {
	exprs.clear();
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
		} catch (const std::exception& e) {
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

    virtual antlrcpp::Any visitModuleapp(BSVParser::ModuleappContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitModuleactualparamarg(BSVParser::ModuleactualparamargContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethoddef(BSVParser::MethoddefContext *ctx) override {
        fprintf(stderr, "    tc MethodDef %s\n", ctx->name->getText().c_str());
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodformals(BSVParser::MethodformalsContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodformal(BSVParser::MethodformalContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMethodcond(BSVParser::MethodcondContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSubinterfacedef(BSVParser::SubinterfacedefContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRuledef(BSVParser::RuledefContext *ctx) override {
        fprintf(stderr, "    tc RuleDef %s\n", ctx->name->getText().c_str());
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulecond(BSVParser::RulecondContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulebody(BSVParser::RulebodyContext *ctx) override {
        return visitChildren(ctx);
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
		    } break;
		    case 2: {
			z3::expr t0 = visit(typeArgs[0]);
			z3::expr t1 = visit(typeArgs[1]);
			bsvtype = decl(t0, t1);
		    } break;
		    default:
			fprintf(stderr, "Too many type arguments: %d\n", numArgs);
		    }
		} else {
		    z3::func_decl bozoDecl = typeDecls.find("Bozo")->second;
		    bsvtype = bozoDecl();
		}
	    }
	} else if (ctx->typenat() != NULL) {
	    return context.int_val((int)strtol(ctx->getText().c_str(), NULL, 0));
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCaseexpr(BSVParser::CaseexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitMatchesexpr(BSVParser::MatchesexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCondexpr(BSVParser::CondexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTripleandexpr(BSVParser::TripleandexprContext *ctx) override {
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
	if (it != exprs.end())
	    return it->second;
	fprintf(stderr, "        Visit binop %s\n", ctx->getText().c_str());

	z3::expr leftsym = visit(ctx->left);
	z3::expr rightsym = visit(ctx->right);

	solver.add(leftsym == rightsym);
	solver.push();
	fprintf(stderr, "        check(%s) %s\n", ctx->getText().c_str(), check_result_name[solver.check()]);
	solver.pop();

	
	std::string opstr(ctx->op->getText());
	char opnamebuf[128];
	snprintf(opnamebuf, sizeof(opnamebuf)-1, "expr%s-%d", opstr.c_str(), nameCount++);
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

	std::string rhsname(ctx->getText() + std::string("$rhs"));
	z3::expr sym = context.constant(context.str_symbol(rhsname.c_str()), typeSort);

	insertExpr(ctx, sym);
	return sym;
    }

    virtual antlrcpp::Any visitBlockexpr(BSVParser::BlockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParfsmexpr(BSVParser::ParfsmexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStructexpr(BSVParser::StructexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStringliteral(BSVParser::StringliteralContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRulesexpr(BSVParser::RulesexprContext *ctx) override {
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

    virtual antlrcpp::Any visitReturnexpr(BSVParser::ReturnexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFieldexpr(BSVParser::FieldexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParenexpr(BSVParser::ParenexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitInterfaceexpr(BSVParser::InterfaceexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionblockexpr(BSVParser::ActionblockexprContext *ctx) override {
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

    virtual antlrcpp::Any visitActionvalueblockexpr(BSVParser::ActionvalueblockexprContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSeqfsmexpr(BSVParser::SeqfsmexprContext *ctx) override {
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

    virtual antlrcpp::Any visitRulesstmt(BSVParser::RulesstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBeginendblock(BSVParser::BeginendblockContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionblock(BSVParser::ActionblockContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitActionvalueblock(BSVParser::ActionvalueblockContext *ctx) override {
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

    virtual antlrcpp::Any visitCasestmtitem(BSVParser::CasestmtitemContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitCasestmtpatitem(BSVParser::CasestmtpatitemContext *ctx) override {
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

    virtual antlrcpp::Any visitForoldinit(BSVParser::ForoldinitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSimplevarassign(BSVParser::SimplevarassignContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFornewinit(BSVParser::FornewinitContext *ctx) override {
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
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitConstantpattern(BSVParser::ConstantpatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitTaggedunionpattern(BSVParser::TaggedunionpatternContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitStructpattern(BSVParser::StructpatternContext *ctx) override {
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

    virtual antlrcpp::Any visitProvisos(BSVParser::ProvisosContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitProviso(BSVParser::ProvisoContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitFsmstmt(BSVParser::FsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitSeqfsmstmt(BSVParser::SeqfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitParfsmstmt(BSVParser::ParfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitIffsmstmt(BSVParser::IffsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitReturnfsmstmt(BSVParser::ReturnfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitWhilefsmstmt(BSVParser::WhilefsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForfsminit(BSVParser::ForfsminitContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitForfsmstmt(BSVParser::ForfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitRepeatfsmstmt(BSVParser::RepeatfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitLoopbodyfsmstmt(BSVParser::LoopbodyfsmstmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitPortide(BSVParser::PortideContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitImportbvi(BSVParser::ImportbviContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvistmt(BSVParser::BvistmtContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBviportopt(BSVParser::BviportoptContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvimethodopt(BSVParser::BvimethodoptContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvimethodname(BSVParser::BvimethodnameContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvimethodnames(BSVParser::BvimethodnamesContext *ctx) override {
        return visitChildren(ctx);
    }

    virtual antlrcpp::Any visitBvischedule(BSVParser::BvischeduleContext *ctx) override {
        return visitChildren(ctx);
    }


};
