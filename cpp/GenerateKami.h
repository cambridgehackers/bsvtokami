//
// Created by Jamey Hicks on 10/28/19.
//

#ifndef BSV_PARSER_GENERATEKAMI_H
#define BSV_PARSER_GENERATEKAMI_H

#include <iostream>
#include <fstream>
#include <memory>
#include <string>
#include "BSVType.h"
#include "Expr.h"
#include "Stmt.h"

using namespace std;

class GenerateKami {
    string filename;
    ofstream out;

public:
    GenerateKami();

    void open(const std::string &basicString);
    void close();

    void generateStmts(std::vector<shared_ptr<struct Stmt>> vector);
    void generateKami(shared_ptr<struct Stmt> stmt, int depth = 0);
    void generateKami(const shared_ptr<Expr> &stmt, int depth = 0, int precedence = 100);

    void generateKami(const shared_ptr<BSVType> &stmt, int depth = 0);

    void generateKami(const shared_ptr<ActionBindingStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<BlockStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<ExprStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<FunctionDefStmt> &functiondef, int depth = 0);

    void generateKami(const shared_ptr<IfStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<ImportStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<InterfaceDeclStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<MethodDeclStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<MethodDefStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<ModuleDefStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<RegReadStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<RegWriteStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<ReturnStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<RuleDefStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<TypedefStructStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<TypedefSynonymStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<VarBindingStmt> &stmt, int depth = 0);

    void generateKami(const shared_ptr<FieldExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<VarExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<CallExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<IntConst> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<OperatorExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<ArraySubExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<EnumUnionStructExpr> &expr, int depth = 0, int precedence = 0);


};


#endif //BSV_PARSER_GENERATEKAMI_H
