//
// Created by Jamey Hicks on 2019-07-25.
//

#ifndef BSV_PARSER_GENERATEIR_H
#define BSV_PARSER_GENERATEIR_H

#include <iostream>
#include <fstream>
#include <map>
#include <string>

#include "Stmt.h"
#include "Expr.h"
#include "BSVType.h"

using namespace std;

class GenerateIR {
    ofstream out;
    map<string, int> op_precedences;
public:
    GenerateIR() {}

    ~GenerateIR() {}

    void open(string filename);

    void close();

    void generateIR(const vector<shared_ptr<Stmt>> &package_stmts, int depth = 0);

    void generateIR(const shared_ptr<Stmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<Expr> &stmt, int depth = 0, int precedence = 100);

    void generateIR(const shared_ptr<BSVType> &stmt, int depth = 0);

    void generateIR(const shared_ptr<ActionBindingStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<BlockStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<ExprStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<IfStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<ImportStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<InterfaceDeclStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<MethodDeclStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<MethodDefStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<ModuleDefStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<RegWriteStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<ReturnStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<RuleDefStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<TypedefStructStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<TypedefSynonymStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<VarBindingStmt> &stmt, int depth = 0);

    void generateIR(const shared_ptr<FieldExpr> &expr, int depth = 0, int precedence = 0);

    void generateIR(const shared_ptr<VarExpr> &expr, int depth = 0, int precedence = 0);

    void generateIR(const shared_ptr<CallExpr> &expr, int depth = 0, int precedence = 0);

    void generateIR(const shared_ptr<IntConst> &expr, int depth = 0, int precedence = 0);

    void generateIR(const shared_ptr<OperatorExpr> &expr, int depth = 0, int precedence = 0);

    void generateIR(const shared_ptr<ArraySubExpr> &expr, int depth = 0, int precedence = 0);

    void generateIR(const shared_ptr<EnumUnionStructExpr> &expr, int depth = 0, int precedence = 0);

};

#endif //BSV_PARSER_GENERATEIR_H
