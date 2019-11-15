
#include "TypeChecker.h"

const char *TypeChecker::check_result_name[] = {
        "unsat", "sat", "unknown"
};

void TypeChecker::setupZ3Context() {
    exprs.clear();
    trackers.clear();
    typeDecls.clear();

    intSort = context.int_sort();
    boolSort = context.bool_sort();

    Z3_constructor action_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Action"),
                                                  Z3_mk_string_symbol(context, "isAction"),
                                                  0, NULL, NULL, NULL);
    Z3_symbol actionvalue_field_names[] = {Z3_mk_string_symbol(context, "elt")};
    Z3_sort actionvalue_field_sorts[] = {NULL};
    unsigned actionvalue_field_sort_refs[] = {0};
    Z3_constructor actionvalue_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "ActionValue"),
                                                       Z3_mk_string_symbol(context, "isActionValue"),
                                                       1,
                                                       actionvalue_field_names,
                                                       actionvalue_field_sorts,
                                                       actionvalue_field_sort_refs);
    Z3_symbol bit_field_names[] = {Z3_mk_string_symbol(context, "width")};
    Z3_sort bit_field_sorts[] = {intSort};
    unsigned bit_field_sort_refs[] = {0};
    Z3_constructor bit_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Bit"),
                                               Z3_mk_string_symbol(context, "isBit"),
                                               1,
                                               bit_field_names,
                                               bit_field_sorts,
                                               bit_field_sort_refs);
    Z3_constructor bool_con = Z3_mk_constructor(context,
                                                Z3_mk_string_symbol(context, "Bool"),
                                                Z3_mk_string_symbol(context, "isBool"),
                                                0, NULL, NULL, NULL);
    Z3_constructor bozo_con = Z3_mk_constructor(context,
                                                Z3_mk_string_symbol(context, "Bozo"),
                                                Z3_mk_string_symbol(context, "isBozo"),
                                                0, NULL, NULL, NULL);
    Z3_symbol function_field_names[] = {Z3_mk_string_symbol(context, "domain"), Z3_mk_string_symbol(context, "range")};
    Z3_sort function_field_sorts[] = {NULL, NULL};
    unsigned function_field_sort_refs[] = {0, 0};
    Z3_constructor function_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Function"),
                                                    Z3_mk_string_symbol(context, "isFunction"),
                                                    2,
                                                    function_field_names,
                                                    function_field_sorts,
                                                    function_field_sort_refs);
    Z3_constructor integer_con = Z3_mk_constructor(context,
                                                   Z3_mk_string_symbol(context, "Integer"),
                                                   Z3_mk_string_symbol(context, "isInteger"),
                                                   0, NULL, NULL, NULL);
    Z3_constructor real_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Real"),
                                                Z3_mk_string_symbol(context, "isReal"),
                                                0, NULL, NULL, NULL);
    Z3_symbol reg_field_names[] = {Z3_mk_string_symbol(context, "elt")};
    Z3_sort reg_field_sorts[] = {NULL};
    unsigned reg_field_sort_refs[] = {0};
    Z3_constructor reg_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Reg"),
                                               Z3_mk_string_symbol(context, "isReg"),
                                               1,
                                               reg_field_names,
                                               reg_field_sorts,
                                               reg_field_sort_refs);
    Z3_constructor rule_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Rule"),
                                                Z3_mk_string_symbol(context, "isRule"),
                                                0, NULL, NULL, NULL);
    Z3_constructor string_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "String"),
                                                  Z3_mk_string_symbol(context, "isString"),
                                                  0, NULL, NULL, NULL);
    Z3_constructor void_con = Z3_mk_constructor(context, Z3_mk_string_symbol(context, "Void"),
                                                Z3_mk_string_symbol(context, "isVoid"),
                                                0, NULL, NULL, NULL);


    Z3_constructor default_constructors[] = {
            action_con, actionvalue_con, bit_con, bool_con, bozo_con, function_con,
            integer_con, real_con, reg_con, rule_con, string_con, void_con
    };
    unsigned num_default_constructors = sizeof(default_constructors) / sizeof(default_constructors[0]);
    // constructors for user-defined types
    unsigned num_constructors = num_default_constructors + typeDeclarationList.size();
    Z3_constructor *constructors = new Z3_constructor[num_constructors];

    for (int i = 0; i < num_default_constructors; i++)
        constructors[i] = default_constructors[i];

    for (int i = 0; i < typeDeclarationList.size(); i++) {
        std::shared_ptr<Declaration> typeDecl(typeDeclarationList[i]);
        std::string typePredicate(std::string("is_") + typeDecl->name);
        fprintf(stderr, "User defined type %s predicate %s\n", typeDecl->name.c_str(), typePredicate.c_str());
        constructors[i + num_default_constructors] = Z3_mk_constructor(context,
                                                                       Z3_mk_string_symbol(context,
                                                                                           typeDecl->name.c_str()),
                                                                       Z3_mk_string_symbol(context,
                                                                                           typePredicate.c_str()),
                //FIXME type parameters
                                                                       0, NULL, NULL, NULL);
    }

    fprintf(stderr, "Defining typeSort\n");
    typeSort = z3::sort(context, Z3_mk_datatype(context, Z3_mk_string_symbol(context, "BSVType"),
                                                num_constructors,
                                                constructors));

    for (unsigned i = 0; i < num_constructors; i++) {
        Z3_func_decl func_decl = Z3_get_datatype_sort_constructor(context, typeSort, i);
        Z3_func_decl recognizer = Z3_get_datatype_sort_recognizer(context, typeSort, i);
        Z3_symbol name = Z3_get_decl_name(context, func_decl);
        fprintf(stderr, "Constructor %d name is %s\n", i, Z3_get_symbol_string(context, name));
        // since no default constructor for z3::func_decl, use insert with a pair
        z3::func_decl func_decl_obj = z3::func_decl(context, func_decl);
        z3::func_decl func_recognizer_obj = z3::func_decl(context, recognizer);
        typeDecls.insert(std::pair<std::string, z3::func_decl>(Z3_get_symbol_string(context, name), func_decl_obj));
        typeRecognizers.insert(std::pair<std::string, z3::func_decl>(Z3_get_symbol_string(context, name), func_recognizer_obj));
        fprintf(stderr, "               name is %s\n", func_decl_obj.name().str().c_str());
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
    cerr << "  insert expr " << ctx->getText().c_str() << endl;
    exprs.insert(std::pair<antlr4::ParserRuleContext *, z3::expr>(ctx, expr));
}

void TypeChecker::insertTracker(antlr4::ParserRuleContext *ctx, z3::expr tracker) {
    cerr << "  insert tracker " << ctx->getText().c_str() << endl;
    trackers.insert(std::pair<antlr4::ParserRuleContext *, z3::expr>(ctx, tracker));
}

z3::expr TypeChecker::orExprs(std::vector<z3::expr> exprs) {
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
