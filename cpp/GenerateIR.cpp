//
// Created by Jamey Hicks on 2019-07-25.
//

#include "GenerateIR.h"
#include <ios>

void GenerateIR::open(string filename) {
    out.open(filename);
    op_precedences["!"] = 3;
    op_precedences["~"] = 3;
    op_precedences["."] = 4; // field expr
    op_precedences["*"] = 5;
    op_precedences["/"] = 5;
    op_precedences["%"] = 5;
    op_precedences["+"] = 6;
    op_precedences["-"] = 6;
    op_precedences["<<"] = 7;
    op_precedences[">>"] = 7;
    // C++ <=> is 8
    op_precedences["<="] = 9;
    op_precedences[">="] = 9;
    op_precedences["<"] = 9;
    op_precedences[">"] = 9;
    op_precedences["=="] = 10;
    op_precedences["!="] = 10;
    op_precedences["&"] = 11;
    op_precedences["|"] = 12;
    op_precedences["&&"] = 13;
    op_precedences["||"] = 14;
    op_precedences[","] = 17;

}

void GenerateIR::close() {
    out.close();
}

void GenerateIR::generateIR(const vector<shared_ptr<Stmt>> &stmts, int depth) {
    for (size_t i = 0; i < stmts.size(); i++) {
        generateIR(stmts[i], depth);
    }
}

void GenerateIR::generateIR(const shared_ptr<Stmt> &stmt, int depth) {
    if (shared_ptr<ActionBindingStmt> actionBindingStmt = stmt->actionBindingStmt()) {
        generateIR(actionBindingStmt, depth);
    } else if (shared_ptr<VarBindingStmt> varBindingStmt = stmt->varBindingStmt()) {
        generateIR(varBindingStmt, depth);
    } else if (shared_ptr<BlockStmt> blockStmt = stmt->blockStmt()) {
        generateIR(blockStmt, depth);
    } else if (shared_ptr<ExprStmt> exprStmt = stmt->exprStmt()) {
        generateIR(exprStmt, depth);
    } else if (shared_ptr<IfStmt> ifStmt = stmt->ifStmt()) {
        generateIR(ifStmt, depth);
    } else if (shared_ptr<ImportStmt> importStmt = stmt->importStmt()) {
        generateIR(importStmt, depth);
    } else if (shared_ptr<InterfaceDeclStmt> interfaceDeclStmt = stmt->interfaceDeclStmt()) {
        generateIR(interfaceDeclStmt, depth);
    } else if (shared_ptr<MethodDeclStmt> methodDeclStmt = stmt->methodDeclStmt()) {
        generateIR(methodDeclStmt, depth);
    } else if (shared_ptr<MethodDefStmt> methodDefStmt = stmt->methodDefStmt()) {
        generateIR(methodDefStmt, depth);
    } else if (shared_ptr<ModuleDefStmt> moduleDefStmt = stmt->moduleDefStmt()) {
        generateIR(moduleDefStmt, depth);
    } else if (shared_ptr<RegWriteStmt> regWriteStmt = stmt->regWriteStmt()) {
        generateIR(regWriteStmt, depth);
    } else if (shared_ptr<ReturnStmt> returnStmt = stmt->returnStmt()) {
        generateIR(returnStmt, depth);
    } else if (shared_ptr<RuleDefStmt> ruleDefStmt = stmt->ruleDefStmt()) {
        generateIR(ruleDefStmt, depth);
    } else if (shared_ptr<TypedefStructStmt> typedefStructStmt = stmt->typedefStructStmt()) {
        generateIR(typedefStructStmt, depth);
    } else if (shared_ptr<TypedefSynonymStmt> typedefSynonymStmt = stmt->typedefSynonymStmt()) {
        generateIR(typedefSynonymStmt, depth);
    }
}

void GenerateIR::generateIR(const shared_ptr<Expr> &expr, int depth, int precedence) {
    if (shared_ptr<FieldExpr> fieldExpr = expr->fieldExpr()) {
        generateIR(fieldExpr, depth);
    } else if (shared_ptr<VarExpr> varExpr = expr->varExpr()) {
        generateIR(varExpr, depth);
    } else if (shared_ptr<CallExpr> callExpr = expr->callExpr()) {
        generateIR(callExpr, depth);
    } else if (shared_ptr<IntConst> intConst = expr->intConst()) {
        generateIR(intConst, depth);
    } else if (shared_ptr<OperatorExpr> operatorExpr = expr->operatorExpr()) {
        generateIR(operatorExpr, depth);
    } else if (shared_ptr<ArraySubExpr> arraySubExpr = expr->arraySubExpr()) {
        generateIR(arraySubExpr, depth);
    } else if (shared_ptr<EnumUnionStructExpr> enumUnionStructExpr = expr->enumUnionStructExpr()) {
        generateIR(enumUnionStructExpr, depth);
    }
}

void GenerateIR::generateIR(const shared_ptr<BSVType> &bsvtype, int depth) {
    out << bsvtype->name;
    if (bsvtype->params.size()) {
        out << "<";
        for (size_t i = 0; i < bsvtype->params.size(); i++) {
            if (i > 0)
                out << ", ";
            generateIR(bsvtype->params[i], depth + 1);
        }
        out << ">";
    }
}


void GenerateIR::generateIR(const shared_ptr<ActionBindingStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    generateIR(stmt->bsvtype, depth);
    out << " " << stmt->name << " <- ";
    generateIR(stmt->rhs, depth);
    out << endl;
}

void GenerateIR::generateIR(const shared_ptr<BlockStmt> &stmt, int depth) {
    out << "{" << endl;
    generateIR(stmt->stmts, depth + 1);
    indent(out, 4 * depth);
    out << "}" << endl;
}

void GenerateIR::generateIR(const shared_ptr<ExprStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    generateIR(stmt->value, depth + 1);
    out << ":" << endl;
}

void GenerateIR::generateIR(const shared_ptr<IfStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "if (";
    generateIR(stmt->condition, depth);
    out << ") ";
    generateIR(stmt->thenStmt, depth);
    indent(out, 4 * depth);
    out << "else ";
    generateIR(stmt->elseStmt, depth);
    out << endl;
}

void GenerateIR::generateIR(const shared_ptr<ImportStmt> &stmt, int depth) {

}

void GenerateIR::generateIR(const shared_ptr<InterfaceDeclStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "INTERFACE " << stmt->name << " {" << endl;
    for (size_t i = 0; i < stmt->decls.size(); i++) {
        generateIR(stmt->decls[i], depth + 1);
    }
    indent(out, 4 * depth);
    out << "}" << endl;
}

void GenerateIR::generateIR(const shared_ptr<MethodDeclStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "METHOD";
    if (stmt->returnType->name == "Action")
        out << "/Action";
    out << " " << stmt->name;
    if (stmt->params.size()) {
        out << " " << "(";
        for (size_t i = 0; i < stmt->params.size(); i++) {
            if (i > 0)
                out << ",";
            out << " ";
            generateIR(stmt->paramTypes[i], depth + 1);
            out << " " << stmt->params[i];
        }
        out << ")";
    }
    out << " ";
    if (stmt->returnType->name != "Action")
        generateIR(stmt->returnType);
    out << endl;
}

void GenerateIR::generateIR(const shared_ptr<MethodDefStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "METHOD";
    if (stmt->returnType->name == "Action")
        out << "/Action";
    out << " " << stmt->name;

    if (stmt->params.size()) {
        out << " " << "(";
        for (size_t i = 0; i < stmt->params.size(); i++) {
            if (i > 0)
                out << ",";
            out << " ";
            generateIR(stmt->paramTypes[i]);
            out << " " << stmt->params[i];
        }
        out << ")";
    }
    out << " ";
    if (stmt->returnType->name != "Action")
        generateIR(stmt->returnType);

    if (stmt->guard) {
        out << " if (";
        generateIR(stmt->guard);
        out << ")";
    }
    out << "{" << endl;
    //FIXME: insert ALLOCAs
    // insert stmts
    for (size_t i = 0; i < stmt->stmts.size(); i++) {
        generateIR(stmt->stmts[i], depth + 1);
    }
    indent(out, 4 * depth);
    out << "}" << endl;
}

void GenerateIR::generateIR(const shared_ptr<ModuleDefStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "MODULE " << stmt->name << " {" << endl;
    for (size_t i = 0; i < stmt->params.size(); i++) {
        indent(out, 4 * depth + 4);
        out << "INTERFACE/Ptr ";
        generateIR(stmt->paramTypes[i], depth + 1);
        out << " " << stmt->params[i] << endl;
    }
    for (size_t i = 0; i < stmt->stmts.size(); i++) {
        if (shared_ptr<ActionBindingStmt> actionBindingStmt = stmt->stmts[i]->actionBindingStmt()) {
            indent(out, 4 * depth + 4);
            out << "FIELD ";
            generateIR(actionBindingStmt->bsvtype, depth);
            out << " " << actionBindingStmt->name << endl;
        } else if (shared_ptr<VarBindingStmt> varBindingStmt = stmt->stmts[i]->varBindingStmt()) {
            indent(out, 4 * depth + 4);
            out << "ALLOCA ";
            generateIR(varBindingStmt->bsvtype, depth);
            out << " " << varBindingStmt->name << endl;
        }
    }
    for (size_t i = 0; i < stmt->stmts.size(); i++) {
        generateIR(stmt->stmts[i], depth + 1);
    }
    indent(out, 4 * depth);
    out << "}" << endl;
}

void GenerateIR::generateIR(const shared_ptr<RegWriteStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "STORE :" << stmt->regName << " = ";
    generateIR(stmt->rhs);
    out << endl;
}

void GenerateIR::generateIR(const shared_ptr<ReturnStmt> &stmt, int depth) {

}

void GenerateIR::generateIR(const shared_ptr<RuleDefStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "METHOD/Rule/Action RULE$" << stmt->name;
    if (stmt->guard) {
        out << " if (";
        generateIR(stmt->guard, depth + 1);
        out << ")";
    }
    out << " {" << endl;
    for (size_t i = 0; i < stmt->stmts.size(); i++) {
        if (shared_ptr<VarBindingStmt> varBindingStmt = stmt->stmts[i]->varBindingStmt()) {
            indent(out, 4 * depth + 4);
            out << "ALLOCA ";
            generateIR(varBindingStmt->bsvtype, depth);
            out << " " << varBindingStmt->name << endl;
        }
    }
    generateIR(stmt->stmts, depth + 1);
    indent(out, 4 * depth);
    out << "}" << endl;
}

void GenerateIR::generateIR(const shared_ptr<TypedefStructStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    out << "STRUCT " << stmt->name << " {" << endl;
    indent(out, 4 * depth);
    for (size_t i = 0; i < stmt->members.size(); i++) {
        indent(out, 4 * depth + 4);
        out << "FIELD ";
        generateIR(stmt->memberTypes[i]);
        out << " " << stmt->members[i] << endl;
    }
    out << "}" << endl;
}

void GenerateIR::generateIR(const shared_ptr<TypedefSynonymStmt> &stmt, int depth) {

}

void GenerateIR::generateIR(const shared_ptr<VarBindingStmt> &stmt, int depth) {
    indent(out, 4 * depth);
    //generateIR(stmt->bsvtype, depth);
    out << stmt->name << " = ";
    generateIR(stmt->rhs, depth);
    out << endl;
}

void GenerateIR::generateIR(const shared_ptr<FieldExpr> &expr, int depth, int level) {
    generateIR(expr->object, depth, 0);
    out << "." << expr->fieldName;
}

void GenerateIR::generateIR(const shared_ptr<VarExpr> &expr, int depth, int level) {
    out << expr->name;
}

void GenerateIR::generateIR(const shared_ptr<CallExpr> &expr, int depth, int level) {
    generateIR(expr->function, depth, 0);
    out << "(";
    for (size_t i = 0; i < expr->args.size(); i++) {
        if (i > 0)
            out << ", ";
        generateIR(expr->args[i], depth + 1, 100);
    }
    out << ")";
}

void GenerateIR::generateIR(const shared_ptr<IntConst> &expr, int depth, int level) {
    //FIXME: base
    if (expr->base && expr->base != 10)
        out << std::hex;
    out << "0x" << expr->value;
    if (expr->base && expr->base != 10)
        out << std::dec;
}

void GenerateIR::generateIR(const shared_ptr<OperatorExpr> &expr, int depth, int level) {
    //FIXME: precedence
    int op_precedence = op_precedences.find(expr->op)->second;
    if (op_precedence > level)
        out << "(";
    if (!expr->rhs)
        out << expr->op << " ";
    generateIR(expr->lhs, depth + 1);
    if (expr->rhs) {
        out << " " << expr->op << " ";
        generateIR(expr->rhs);
    }
    if (op_precedence > level)
        out << ")";
}

void GenerateIR::generateIR(const shared_ptr<ArraySubExpr> &expr, int depth, int level) {
    generateIR(expr->array, depth, 0);
    out << "[";
    generateIR(expr->msb, depth, 0);
    if (expr->lsb) {
        out << ",";
        generateIR(expr->lsb, depth, 0);
    }
    out << "]";
}

void GenerateIR::generateIR(const shared_ptr<EnumUnionStructExpr> &expr, int depth, int level) {
    out << expr->tag;
    //FIXME: keys and values, struct vs union
    if (expr->keys.size()) {
        out << " {";
        for (size_t i = 0; i < expr->keys.size(); i++) {
            out << expr->keys[i];
            out << ": ";
            generateIR(expr->vals[i]);
        }
        out << " }";
    }
}
