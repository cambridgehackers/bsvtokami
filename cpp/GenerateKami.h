//
// Created by Jamey Hicks on 10/28/19.
//

#ifndef BSV_PARSER_GENERATEKAMI_H
#define BSV_PARSER_GENERATEKAMI_H

#include <iostream>
#include <fstream>
#include <map>
#include <memory>
#include <string>
#include "BSVType.h"
#include "Expr.h"
#include "Stmt.h"

using namespace std;

class GenerateKami {
    string filename;
    ofstream out;
    ofstream logstream;
    map<string,string> instanceNames;
    map<string,string> coqTypeMapping;
    map<string,string> kamiTypeMapping;

    bool actionContext;
    string returnPending; // a bit of a hack

public:
    GenerateKami();

    void open(const std::string &basicString);
    void close();

    void generateStmts(std::vector<shared_ptr<struct Stmt>> vector, int depth);

    void generateModuleStmt(const shared_ptr<struct Stmt> &stmt, int depth, vector<shared_ptr<Stmt>> &actionStmts);

    // void generateModuleStmt(const shared_ptr<ActionBindingStmt> &actionbinding, int depth);

    // void generateModuleStmt(const shared_ptr<CallStmt> &actionbinding, int depth);

    void generateModuleStmt(const shared_ptr<MethodDefStmt> &methoddef, int depth, vector<shared_ptr<Stmt>> &actionStmts);

    void generateModuleStmt(const shared_ptr<RegisterStmt> &registerStmt, int depth, vector<shared_ptr<Stmt>> &actionStmts);

    void generateModuleStmt(const shared_ptr<RuleDefStmt> &stmt, int depth, vector<shared_ptr<Stmt>> &actionStmts);

    void generateModuleStmt(const shared_ptr<VarBindingStmt> &stmt, int depth);

    void generateKami(const shared_ptr<struct Stmt> &stmt, int depth);

    void generateCoqType(ostream &ostr, const shared_ptr<BSVType> &bsvtype, int depth);

    void generateCoqType(const shared_ptr<BSVType> &bsvtype, int depth);

    void generateKami(const shared_ptr<BSVType> &stmt, int depth);

    void generateKami(const shared_ptr<ActionBindingStmt> &stmt, int depth);

    void generateKami(const shared_ptr<BlockStmt> &stmt, int depth);

    void generateKami(const shared_ptr<CallStmt> &stmt, int depth);

    void generateKami(const shared_ptr<ExprStmt> &stmt, int depth);

    void generateKami(const shared_ptr<FunctionDefStmt> &functiondef, int depth);

    void generateKami(const shared_ptr<IfStmt> &stmt, int depth);

    void generateKami(const shared_ptr<ImportStmt> &stmt, int depth);

    void generateKami(const shared_ptr<InterfaceDeclStmt> &stmt, int depth);

    void generateKami(const shared_ptr<MethodDeclStmt> &stmt, int depth);

    void generateKami(const shared_ptr<MethodDefStmt> &stmt, int depth);

    void generateKami(const shared_ptr<ModuleDefStmt> &stmt, int depth);

    void generateKami(const shared_ptr<RegReadStmt> &stmt, int depth);

    void generateKami(const shared_ptr<RegWriteStmt> &stmt, int depth);

    void generateKami(const shared_ptr<ReturnStmt> &stmt, int depth);

    void generateKami(const shared_ptr<TypedefEnumStmt> &stmt, int depth);

    void generateKami(const shared_ptr<TypedefStructStmt> &stmt, int depth);

    void generateKami(const shared_ptr<TypedefSynonymStmt> &stmt, int depth);

    void generateKami(const shared_ptr<VarAssignStmt> &stmt, int depth);

    void generateKami(const shared_ptr<VarBindingStmt> &stmt, int depth);

    void generateKami(const shared_ptr<Expr> &stmt, int depth = 0, int precedence = 100);

    void generateKami(const shared_ptr<FieldExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<MethodExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<SubinterfaceExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<VarExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<CallExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<IntConst> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<OperatorExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<ArraySubExpr> &expr, int depth = 0, int precedence = 0);

    void generateKami(const shared_ptr<BitSelExpr> &expr, int depth, int precedence);

    void generateKami(const shared_ptr<EnumUnionStructExpr> &expr, int depth = 0, int precedence = 0);

    void generateMethodName(const shared_ptr<Expr> &expr);

    string callStmtFunctionName(const shared_ptr<CallStmt> &callStmt);

    std::vector<shared_ptr<struct Stmt>> sortStmts(vector<shared_ptr<struct Stmt>> vector);

    void generateKamiLHS(const shared_ptr<Expr> &expr);

    void generateKamiLHS(const shared_ptr<LValue> &lvalue);

    string formatStructDecl(const map<string,shared_ptr<BSVType>> &assignedVars);
};


#endif //BSV_PARSER_GENERATEKAMI_H
