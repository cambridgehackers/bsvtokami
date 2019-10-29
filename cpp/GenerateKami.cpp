//
// Created by Jamey Hicks on 10/28/19.
//

#include "GenerateKami.h"


GenerateKami::GenerateKami() {

}

void GenerateKami::open(const string &filename) {
    this->filename = filename;
    out.open(filename);
}

void GenerateKami::close() {
    out.close();
}

void GenerateKami::generateStmts(std::vector<shared_ptr<struct Stmt>> stmts) {
    for (int i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt = stmts[i];
        generateKami(stmt);
    }

}

void GenerateKami::generateKami(shared_ptr<Stmt> stmt, int depth) {
    if (shared_ptr<ActionBindingStmt> actionBindingStmt = stmt->actionBindingStmt()) {
        generateKami(actionBindingStmt, depth);
    } else if (shared_ptr<VarBindingStmt> varBindingStmt = stmt->varBindingStmt()) {
        generateKami(varBindingStmt, depth);
    } else if (shared_ptr<BlockStmt> blockStmt = stmt->blockStmt()) {
        generateKami(blockStmt, depth);
    } else if (shared_ptr<ExprStmt> exprStmt = stmt->exprStmt()) {
        generateKami(exprStmt, depth);
    } else if (shared_ptr<IfStmt> ifStmt = stmt->ifStmt()) {
        generateKami(ifStmt, depth);
    } else if (shared_ptr<ImportStmt> importStmt = stmt->importStmt()) {
        generateKami(importStmt, depth);
    } else if (shared_ptr<InterfaceDeclStmt> interfaceDeclStmt = stmt->interfaceDeclStmt()) {
        generateKami(interfaceDeclStmt, depth);
    } else if (shared_ptr<MethodDeclStmt> methodDeclStmt = stmt->methodDeclStmt()) {
        generateKami(methodDeclStmt, depth);
    } else if (shared_ptr<MethodDefStmt> methodDefStmt = stmt->methodDefStmt()) {
        generateKami(methodDefStmt, depth);
    } else if (shared_ptr<ModuleDefStmt> moduleDefStmt = stmt->moduleDefStmt()) {
        generateKami(moduleDefStmt, depth);
    } else if (shared_ptr<RegWriteStmt> regWriteStmt = stmt->regWriteStmt()) {
        generateKami(regWriteStmt, depth);
    } else if (shared_ptr<ReturnStmt> returnStmt = stmt->returnStmt()) {
        generateKami(returnStmt, depth);
    } else if (shared_ptr<RuleDefStmt> ruleDefStmt = stmt->ruleDefStmt()) {
        generateKami(ruleDefStmt, depth);
    } else if (shared_ptr<TypedefStructStmt> typedefStructStmt = stmt->typedefStructStmt()) {
        generateKami(typedefStructStmt, depth);
    } else if (shared_ptr<TypedefSynonymStmt> typedefSynonymStmt = stmt->typedefSynonymStmt()) {
        generateKami(typedefSynonymStmt, depth);
    }
}


void GenerateKami::generateKami(const shared_ptr<Expr> &expr, int depth, int precedence) {
    out << "Expr" << "{ ";
    expr->prettyPrint(depth);
    out << " }" << endl;
}

void GenerateKami::generateKami(const shared_ptr<BSVType> &bsvtype, int depth) {
    out << "bsvtype" << "{ ";
    bsvtype->prettyPrint(depth);
    out << " }" << endl;
}

void GenerateKami::generateKami(const shared_ptr<ActionBindingStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<BlockStmt> &blockstmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<ExprStmt> &stmt, int depth) {
    generateKami(stmt->expr, depth);
}

void GenerateKami::generateKami(const shared_ptr<IfStmt> &stmt, int depth) {
    out << "If (";
    generateKami(stmt->condition, depth + 1);
    out << ") then (" << endl;
    generateKami(stmt->thenStmt, depth + 1);
    out << ") else (" << endl;
    generateKami(stmt->elseStmt, depth + 1);
    out << ") as v; Ret v" << endl;
}

void GenerateKami::generateKami(const shared_ptr<ImportStmt> &stmt, int depth) {
    out << "(* import " << stmt->name << " *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<InterfaceDeclStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<MethodDeclStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<MethodDefStmt> &stmt, int depth) {
    indent(out, depth);
    out << "with Method (instancePrefix--\"" << stmt->name << "\") (* args *) (* result type *) := " << endl;
    indent(out, depth); out << "(" << endl;
    indent(out, depth); out << ")" << endl;
}

void GenerateKami::generateKami(const shared_ptr<ModuleDefStmt> &moduledef, int depth) {
    indent(out, depth);
    out << "Module module'" << moduledef->name << "." << endl;
    indent(out, depth + 1);
    out << "(BKMODULE {" << endl;
    indent(out, depth + 1);
    out << "})." << endl;
    out << "End module'" << moduledef->name << "." << endl;
}

void GenerateKami::generateKami(const shared_ptr<RegWriteStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<ReturnStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<RuleDefStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<TypedefStructStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<TypedefSynonymStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<VarBindingStmt> &stmt, int depth) {

}

void GenerateKami::generateKami(const shared_ptr<FieldExpr> &expr, int depth, int precedence) {

}

void GenerateKami::generateKami(const shared_ptr<VarExpr> &expr, int depth, int precedence) {

}

void GenerateKami::generateKami(const shared_ptr<CallExpr> &expr, int depth, int precedence) {

}

void GenerateKami::generateKami(const shared_ptr<IntConst> &expr, int depth, int precedence) {

}

void GenerateKami::generateKami(const shared_ptr<OperatorExpr> &expr, int depth, int precedence) {

}

void GenerateKami::generateKami(const shared_ptr<ArraySubExpr> &expr, int depth, int precedence) {

}

void GenerateKami::generateKami(const shared_ptr<EnumUnionStructExpr> &expr, int depth, int precedence) {

}


