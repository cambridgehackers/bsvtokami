
#include <iostream>

using namespace std;

#include "Stmt.h"

void indent(int depth) {
    for (int i = 0; i < depth; i++)
        cout << " ";
}

Stmt::Stmt(StmtType stmtType)
        : stmtType(stmtType) {
}

RuleDefStmt::RuleDefStmt(string name, shared_ptr<Expr> guard)
        : Stmt(RuleDefStmtType), name(name), guard(guard) {
}

void RuleDefStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "rule " << name;
    if (guard) {
        cout << " when (";
        guard->prettyPrint(0);
        cout << ")";
    }
    cout << ";" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(stmts.at(i));
        if (stmt)
            stmt->prettyPrint(depth + 1);
    }
    indent(4 * depth);
    cout << "endrule //" << name << endl;
}

RegWriteStmt::RegWriteStmt(string regName, shared_ptr<Expr> rhs)
        : Stmt(RegWriteStmtType), regName(regName), rhs(rhs) {
}

void RegWriteStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << regName << " <= ";
    if (rhs)
        rhs->prettyPrint(depth + 1);
    else
        cout << "no_rhs";
    cout << ";" << endl;
}

ActionBindingStmt::ActionBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name,
                               const shared_ptr<Expr> &rhs)
        : Stmt(ActionBindingStmtType), bsvtype(bsvtype), name(name), rhs(rhs) {

}

void ActionBindingStmt::prettyPrint(int depth) {
    indent(4 * depth);
    bsvtype->prettyPrint();
    cout << " " << name << " <- ";
    rhs->prettyPrint(depth + 1);
    cout << ";" << endl;

}

VarBindingStmt::VarBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name,
                               const shared_ptr<Expr> &rhs)
                               : Stmt(VarBindingStmtType), bsvtype(bsvtype), name(name), rhs(rhs) {

}

void VarBindingStmt::prettyPrint(int depth) {
    indent(4 * depth);
    if (bsvtype) bsvtype->prettyPrint();
    cout << " " << name << " = ";
    rhs->prettyPrint(depth + 1);
    cout << ";" << endl;
}

MethodDeclStmt::MethodDeclStmt(const string &name, const shared_ptr<BSVType> &returnType,
                             const std::vector<std::string> &params,
                             const std::vector<std::shared_ptr<BSVType>> &paramTypes)
        : Stmt(MethodDeclStmtType), name(name), returnType(returnType),
          params(params), paramTypes(paramTypes) {}

void MethodDeclStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "method ";
    returnType->prettyPrint(depth + 1);
    cout << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            cout << ", ";
        paramTypes[i]->prettyPrint(depth+1);
        cout << " " << params[i];
    }
    cout << ");" << endl;
}

MethodDefStmt::MethodDefStmt(const string &name, const shared_ptr<BSVType> &returnType,
                             const std::vector<std::string> &params,
                             const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                             const shared_ptr<Expr> &guard,
                             const vector<std::shared_ptr<Stmt>> &stmts)
        : Stmt(MethodDefStmtType), name(name), returnType(returnType),
        params(params), paramTypes(paramTypes),
        guard(guard), stmts(stmts) {}

MethodDefStmt::~MethodDefStmt() {

}

void MethodDefStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "method ";
    returnType->prettyPrint(depth + 1);
    cout << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            cout << ", ";
        paramTypes[i]->prettyPrint(depth+1);
        cout << " " << params[i];
    }
    cout << ");" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        stmts.at(i)->prettyPrint(depth + 1);
    }
    indent(4 * depth);
    cout << "endmethod" << endl;
}

ModuleDefStmt::ModuleDefStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                             const std::vector<std::string> &params,
                             const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                             const std::vector<std::shared_ptr<Stmt>> &stmts)
                             : Stmt(ModuleDefStmtType), name(name),
                               params(params), paramTypes(paramTypes),
                               interfaceType(interfaceType), stmts(stmts) {

}

ModuleDefStmt::~ModuleDefStmt() {

}

void ModuleDefStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "module ";
    interfaceType->prettyPrint(depth + 1);
    cout << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            cout << ", ";
        paramTypes[i]->prettyPrint(depth+1);
        cout << " " << params[i];
    }
    cout << ");" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        stmts.at(i)->prettyPrint(depth + 1);
    }
    indent(4 * depth);
    cout << "endmodule" << endl;
}

IfStmt::IfStmt(const shared_ptr<Expr> &condition, const shared_ptr<Stmt> &thenStmt,
               const shared_ptr<Stmt> &elseStmt) : Stmt(IfStmtType), condition(condition), thenStmt(thenStmt),
                                                   elseStmt(elseStmt) {}

IfStmt::~IfStmt() {

}

void IfStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "if (";
    condition->prettyPrint(depth + 1);
    cout << ") ";
    thenStmt->prettyPrint(depth + 1);
    if (elseStmt) {
        indent(4 * depth);
        cout << "else ";
        elseStmt->prettyPrint(depth + 1);
    }
    cout << endl;
}

BlockStmt::BlockStmt(std::vector<std::shared_ptr<Stmt>> stmts) : Stmt(BlockStmtType), stmts(stmts) {}
BlockStmt::~BlockStmt() {}

void BlockStmt::prettyPrint(int depth) {
    cout << "begin" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        stmts.at(i)->prettyPrint(depth + 1);
    }
    indent(4 * depth);
    cout << "end" << endl;
}


void RetStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "return ";
    value->prettyPrint(depth);
    cout << ";" << endl;
}

void ExprStmt::prettyPrint(int depth) {
    indent(4 * depth);
    value->prettyPrint(depth);
    cout << ";" << endl;
}

ImportStmt::ImportStmt(const std::string name) : Stmt(ImportStmtType), name(name) {

}

void ImportStmt::prettyPrint(int depth) {
    cout << "import " << name << " :: *;" << endl;
}

InterfaceDeclStmt::InterfaceDeclStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                                     const vector<std::shared_ptr<Stmt>> &decls)
                                     : Stmt(InterfaceDeclStmtType), name(name),
                                     interfaceType(interfaceType), decls(decls) {
}

void InterfaceDeclStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "interface ";
    interfaceType->prettyPrint(depth + 1);
    cout << ":" << endl;
    for (size_t i = 0; i < decls.size(); i++) {
        decls[i]->prettyPrint(depth + 1);
    }
    indent(4 * depth);
    cout << "endinterface" << endl;
}

TypedefSynonymStmt::TypedefSynonymStmt(const std::shared_ptr<BSVType> &typedeftype, const std::shared_ptr<BSVType> &type)
    : Stmt(TypedefSynonymStmtType), typedeftype(typedeftype), type(type) {

}

void TypedefSynonymStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "typedef ";
    type->prettyPrint();
    cout << " ";
    typedeftype->prettyPrint();
    cout << ":" << endl;
}

TypedefStructStmt::TypedefStructStmt(const std::string &name, const std::shared_ptr<BSVType> &structType,
                                     const std::vector<std::string> &members,
                                     const std::vector<std::shared_ptr<BSVType>> &memberTypes)
                                     : Stmt(TypedefStructStmtType),
                                     name(name), structType(structType),
                                     members(members), memberTypes(memberTypes) {
}

void TypedefStructStmt::prettyPrint(int depth) {
    indent(4 * depth);
    cout << "typedef struct {" << endl;
    for (size_t i = 0; i < members.size(); i++) {
        indent(4 * (depth + 1));
        memberTypes[i]->prettyPrint(depth + 1);
        cout << " " << members[i] << ";" << endl;
    }
    indent(4 * depth);
    cout << "} ";
    structType->prettyPrint(depth);
    cout << ":" << endl;
}
