//
// Created by Jamey Hicks on 11/7/19.
//

#include "GenerateKoika.h"

#include <string>

GenerateKoika::GenerateKoika() {

}

void GenerateKoika::open(const std::string &filename) {
    this->filename = filename;
    cerr << "Opening Koika file " << filename << endl;
    out.open(filename);
    out << "Require Import Koika.Frontend." << endl;
    out << "Require Import Koika.Std." << endl;
    out << endl;
}

void GenerateKoika::close() {
    cerr << "Closing Koika file " << filename << endl;
    out.close();
}

void GenerateKoika::generateStmts(std::vector<shared_ptr<struct Stmt>> stmts) {
    for (int i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt = stmts[i];
        generateKoika(stmt);
    }
}

void GenerateKoika::generateKoika(shared_ptr<Stmt> stmt, int depth) {
    if (shared_ptr<ActionBindingStmt> actionBindingStmt = stmt->actionBindingStmt()) {
        generateKoika(actionBindingStmt, depth);
    } else if (shared_ptr<VarBindingStmt> varBindingStmt = stmt->varBindingStmt()) {
        generateKoika(varBindingStmt, depth);
    } else if (shared_ptr<BlockStmt> blockStmt = stmt->blockStmt()) {
        generateKoika(blockStmt, depth);
    } else if (shared_ptr<ExprStmt> exprStmt = stmt->exprStmt()) {
        generateKoika(exprStmt, depth);
    } else if (shared_ptr<IfStmt> ifStmt = stmt->ifStmt()) {
        generateKoika(ifStmt, depth);
    } else if (shared_ptr<ImportStmt> importStmt = stmt->importStmt()) {
        generateKoika(importStmt, depth);
    } else if (shared_ptr<InterfaceDeclStmt> interfaceDeclStmt = stmt->interfaceDeclStmt()) {
        generateKoika(interfaceDeclStmt, depth);
    } else if (shared_ptr<MethodDeclStmt> methodDeclStmt = stmt->methodDeclStmt()) {
        generateKoika(methodDeclStmt, depth);
    } else if (shared_ptr<MethodDefStmt> methodDefStmt = stmt->methodDefStmt()) {
        generateKoika(methodDefStmt, depth);
    } else if (shared_ptr<ModuleDefStmt> moduleDefStmt = stmt->moduleDefStmt()) {
        generateKoika(moduleDefStmt, depth);
    } else if (shared_ptr<RegWriteStmt> regWriteStmt = stmt->regWriteStmt()) {
        generateKoika(regWriteStmt, depth);
    } else if (shared_ptr<ReturnStmt> returnStmt = stmt->returnStmt()) {
        generateKoika(returnStmt, depth);
    } else if (shared_ptr<RuleDefStmt> ruleDefStmt = stmt->ruleDefStmt()) {
        generateKoika(ruleDefStmt, depth);
    } else if (shared_ptr<TypedefStructStmt> typedefStructStmt = stmt->typedefStructStmt()) {
        generateKoika(typedefStructStmt, depth);
    } else if (shared_ptr<TypedefSynonymStmt> typedefSynonymStmt = stmt->typedefSynonymStmt()) {
        generateKoika(typedefSynonymStmt, depth);
    }
}

void GenerateKoika::generateKoika(const shared_ptr<Expr> &expr, int depth, int precedence) {
    if (shared_ptr<CallExpr> callExpr = expr->callExpr()) {
        generateKoika(callExpr, depth, 0);
    } else {
        out << "Expr" << "{ ";
        expr->prettyPrint(out, depth);
        out << " }" << endl;
    }
}


void GenerateKoika::generateKoika(const shared_ptr<BSVType> &bsvtype, int depth) {
    out << "bsvtype" << "{ ";
    bsvtype->prettyPrint(out, depth);
    out << " }" << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<ActionBindingStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<BlockStmt> &blockstmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<ExprStmt> &stmt, int depth) {
    indent(out, depth+1);
    generateKoika(stmt->expr, depth+1);
    out << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<IfStmt> &stmt, int depth) {
    out << "If (";
    generateKoika(stmt->condition, depth + 1);
    out << ") then (" << endl;
    generateKoika(stmt->thenStmt, depth + 1);
    out << ") else (" << endl;
    generateKoika(stmt->elseStmt, depth + 1);
    out << ") as v; Ret v" << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<ImportStmt> &stmt, int depth) {
    out << "(* import " << stmt->name << " *)" << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<InterfaceDeclStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<MethodDeclStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<MethodDefStmt> &methoddef, int depth) {
    out << endl;
    indent(out, depth);
    out << "Definition " << methoddef->name << " : uaction (* args *) (* result type *) := " << endl;
    indent(out, depth+1); out << "{{" << endl;

    for (int i = 0; i < methoddef->stmts.size(); i++) {
        shared_ptr<Stmt> stmt = methoddef->stmts[i];
        generateKoika(stmt, depth+1);
    }

    indent(out, depth+1); out << "}}" << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<ModuleDefStmt> &moduledef, int depth) {
    indent(out, depth);
    out << "Module " << moduledef->name << "." << endl;

    for (int i = 0; i < moduledef->stmts.size(); i++) {
        shared_ptr<Stmt> stmt = moduledef->stmts[i];
        generateKoika(stmt, depth+1);
    }

    out << endl;
    out << "End " << moduledef->name << "." << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<RegWriteStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<ReturnStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<RuleDefStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<TypedefStructStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<TypedefSynonymStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<VarBindingStmt> &stmt, int depth) {

}

void GenerateKoika::generateKoika(const shared_ptr<FieldExpr> &expr, int depth, int precedence) {

}

void GenerateKoika::generateKoika(const shared_ptr<VarExpr> &expr, int depth, int precedence) {

}

void GenerateKoika::generateKoika(const shared_ptr<CallExpr> &expr, int depth, int precedence) {
    out << "call ";
    generateKoika(expr->function, depth+1, 0);
    out << "(* args *)" << endl;
}

void GenerateKoika::generateKoika(const shared_ptr<IntConst> &expr, int depth, int precedence) {

}

void GenerateKoika::generateKoika(const shared_ptr<OperatorExpr> &expr, int depth, int precedence) {

}

void GenerateKoika::generateKoika(const shared_ptr<ArraySubExpr> &expr, int depth, int precedence) {

}

void GenerateKoika::generateKoika(const shared_ptr<EnumUnionStructExpr> &expr, int depth, int precedence) {

}