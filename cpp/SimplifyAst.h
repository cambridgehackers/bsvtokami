//
// Created by Jamey Hicks on 11/13/19.
//

#ifndef BSV_PARSER_SIMPLIFYAST_H
#define BSV_PARSER_SIMPLIFYAST_H

#include <map>
#include <memory>
#include <iostream>
#include <string>
#include <fstream>

#include "BSVType.h"
#include "Expr.h"
#include "Stmt.h"

using namespace std;

class SimplifyAst {
    ofstream logstream;
    map<string, shared_ptr<BSVType>> registers; // maps name to the element type of the register
    bool actionContext = false;

public:
    SimplifyAst(const string &packageName) : logstream(string("kami/") + packageName + string(".simpl.txt"), ostream::out) {}

    ~SimplifyAst() {}

    void simplify(const vector<shared_ptr<struct Stmt>> &stmts, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<struct Stmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<struct Stmt> simplifySubstatement(const shared_ptr<struct Stmt> &stmt);

    shared_ptr<Expr> simplify(const shared_ptr<Expr> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<BSVType> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<ActionBindingStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<BlockStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<ExprStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<FunctionDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<IfStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<ImportStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<InterfaceDeclStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<InterfaceDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<MethodDeclStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<MethodDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<ModuleDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<PatternMatchStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<RegReadStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<RegWriteStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<ReturnStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<RuleDefStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<TypedefStructStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<TypedefSynonymStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<VarAssignStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    void simplify(const shared_ptr<VarBindingStmt> &stmt, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<FieldExpr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<VarExpr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<CallExpr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<IntConst> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr> simplify(const shared_ptr<MatchesExpr> &matchesExpr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<OperatorExpr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<ArraySubExpr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  simplify(const shared_ptr<EnumUnionStructExpr> &expr, vector<shared_ptr<struct Stmt>> &simplifiedStmts);

    shared_ptr<Expr>  matchPattern(const shared_ptr<Pattern> &pattern, vector<shared_ptr<struct Stmt>> &simplifiedStmts);


};


#endif //BSV_PARSER_SIMPLIFYAST_H
