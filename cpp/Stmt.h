#pragma once

#include <string>
#include <vector>
#include <map>
#include <memory>
#include <iostream>

using namespace std;

#include "BSVType.h"
#include "Declaration.h"
#include "Expr.h"
#include "LValue.h"
#include "LexicalScope.h"
#include "SourcePos.h"

void indent(ostream &s, int depth);

enum StmtType {
    InvalidStmtType,
    ActionBindingStmtType,
    BlockStmtType,
    CallStmtType,
    ExprStmtType,
    FunctionDefStmtType,
    InterfaceDeclStmtType,
    InterfaceDefStmtType,
    IfStmtType,
    ImportStmtType,
    MethodDeclStmtType,
    MethodDefStmtType,
    ModuleDefStmtType,
    ModuleInstStmtType,
    PackageDefStmtType,
    PatternMatchStmtType,
    RegisterStmtType,
    RegReadStmtType,
    RegWriteStmtType,
    ReturnStmtType,
    TypedefEnumStmtType,
    TypedefStructStmtType,
    TypedefSynonymStmtType,
    VarBindingStmtType,
    VarAssignStmtType,
    RuleDefStmtType
};

class ActionBindingStmt;

class BlockStmt;

class CallStmt;

class ExprStmt;

class FunctionDefStmt;

class IfStmt;

class ImportStmt;

class InterfaceDeclStmt;

class InterfaceDefStmt;

class MethodDeclStmt;

class MethodDefStmt;

class ModuleDefStmt;

class ModuleInstStmt;

class PackageDefStmt;

class PatternMatchStmt;

class RegisterStmt;

class RegReadStmt;

class RegWriteStmt;

class ReturnStmt;

class RuleDefStmt;

class TypedefEnumStmt;

class TypedefStructStmt;

class TypedefSynonymStmt;

class VarBindingStmt;

class VarAssignStmt;

class StmtAttrs {
public:
    set<string> boundVars;
    set<string> assignedVars;
    set<string> freeVars;
};

void uniteSet(set<string> &to, const set<string> &from);
string to_string(const set<string> &s);

class Stmt : public enable_shared_from_this<Stmt> {

public:
    const StmtType stmtType;
    const SourcePos sourcePos;

    Stmt(StmtType stmtType, const SourcePos &sourcePos);

    virtual ~Stmt() {}

    const StmtAttrs &attrs() { return attrs_; }

    virtual void prettyPrint(ostream &out, int depth = 0) = 0;

    virtual shared_ptr<ActionBindingStmt> actionBindingStmt() { return shared_ptr<ActionBindingStmt>(); }

    virtual shared_ptr<BlockStmt> blockStmt() { return shared_ptr<BlockStmt>(); }

    virtual shared_ptr<CallStmt> callStmt() { return shared_ptr<CallStmt>(); }

    virtual shared_ptr<ExprStmt> exprStmt() { return shared_ptr<ExprStmt>(); }

    virtual shared_ptr<FunctionDefStmt> functionDefStmt() { return shared_ptr<FunctionDefStmt>(); }

    virtual shared_ptr<IfStmt> ifStmt() { return shared_ptr<IfStmt>(); }

    virtual shared_ptr<ImportStmt> importStmt() { return shared_ptr<ImportStmt>(); }

    virtual shared_ptr<InterfaceDeclStmt> interfaceDeclStmt() { return shared_ptr<InterfaceDeclStmt>(); }

    virtual shared_ptr<InterfaceDefStmt> interfaceDefStmt() { return shared_ptr<InterfaceDefStmt>(); }

    virtual shared_ptr<MethodDeclStmt> methodDeclStmt() { return shared_ptr<MethodDeclStmt>(); }

    virtual shared_ptr<MethodDefStmt> methodDefStmt() { return shared_ptr<MethodDefStmt>(); }

    virtual shared_ptr<ModuleDefStmt> moduleDefStmt() { return shared_ptr<ModuleDefStmt>(); }

    virtual shared_ptr<ModuleInstStmt> moduleInstStmt() { return shared_ptr<ModuleInstStmt>(); }

    virtual shared_ptr<PackageDefStmt> packageDefStmt() { return shared_ptr<PackageDefStmt>(); }

    virtual shared_ptr<PatternMatchStmt> patternMatchStmt() { return shared_ptr<PatternMatchStmt>(); }

    virtual shared_ptr<RegisterStmt> registerStmt() { return shared_ptr<RegisterStmt>(); }

    virtual shared_ptr<RegReadStmt> regReadStmt() { return shared_ptr<RegReadStmt>(); }

    virtual shared_ptr<RegWriteStmt> regWriteStmt() { return shared_ptr<RegWriteStmt>(); }

    virtual shared_ptr<ReturnStmt> returnStmt() { return shared_ptr<ReturnStmt>(); }

    virtual shared_ptr<RuleDefStmt> ruleDefStmt() { return shared_ptr<RuleDefStmt>(); }

    virtual shared_ptr<TypedefEnumStmt> typedefEnumStmt() { return shared_ptr<TypedefEnumStmt>(); }

    virtual shared_ptr<TypedefStructStmt> typedefStructStmt() { return shared_ptr<TypedefStructStmt>(); }

    virtual shared_ptr<TypedefSynonymStmt> typedefSynonymStmt() { return shared_ptr<TypedefSynonymStmt>(); }

    virtual shared_ptr<VarBindingStmt> varBindingStmt() { return shared_ptr<VarBindingStmt>(); }

    virtual shared_ptr<VarAssignStmt> varAssignStmt() { return shared_ptr<VarAssignStmt>(); };

    virtual shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope);

    StmtAttrs attrs_;
};

class ImportStmt : public Stmt {
public:
    ImportStmt(const string &name, const SourcePos &sourcePos = SourcePos());

    ~ImportStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<ImportStmt> importStmt() override;

    const string name;
};

class TypedefEnumStmt : public Stmt {
public:
    TypedefEnumStmt(const string &package, const string &name, const shared_ptr<BSVType> &enumType,
                      const vector<string> &members,
                      const SourcePos &sourcePos = SourcePos());

    virtual ~TypedefEnumStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<TypedefEnumStmt> typedefEnumStmt() override;

public:
    const string package;
    const string name;
    const shared_ptr<BSVType> enumType;
    const vector<string> members;
};

class TypedefSynonymStmt : public Stmt {
public:
    TypedefSynonymStmt(const string &package, const shared_ptr<BSVType> &typedeftype, const shared_ptr<BSVType> &type,
                       const SourcePos &sourcePos = SourcePos());

    ~TypedefSynonymStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<TypedefSynonymStmt> typedefSynonymStmt() override;

public:
    const string package;
    const shared_ptr<BSVType> typedeftype; // type being defined
    const shared_ptr<BSVType> type;
};

class TypedefStructStmt : public Stmt {
public:
    TypedefStructStmt(const string &package, const string &name, const shared_ptr<BSVType> &structType,
                      const vector<string> &members,
                      const vector<shared_ptr<BSVType>> &memberTypes,
                      const SourcePos &sourcePos = SourcePos());

    virtual ~TypedefStructStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<TypedefStructStmt> typedefStructStmt() override;

public:
    const string package;
    const string name;
    const shared_ptr<BSVType> structType;
    const vector<string> members;
    const vector<shared_ptr<BSVType>> memberTypes;
};

class InterfaceDeclStmt : public Stmt {
public:
    InterfaceDeclStmt(const string &package, const string &name, const shared_ptr<BSVType> &interfaceType,
                      const vector<shared_ptr<Stmt>> &decls,
                      const SourcePos &sourcePos = SourcePos());

    ~InterfaceDeclStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<InterfaceDeclStmt> interfaceDeclStmt() override;

    const string package;
    const string name;
    const shared_ptr<BSVType> interfaceType;
    const vector<shared_ptr<Stmt>> decls;
};

class InterfaceDefStmt : public Stmt {
public:
    InterfaceDefStmt(const string &package, const string &name, const shared_ptr<BSVType> &interfaceType,
                     const vector<shared_ptr<Stmt>> &defs,
                     const SourcePos &sourcePos = SourcePos());

    ~InterfaceDefStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<InterfaceDefStmt> interfaceDefStmt() override;

    const string package;
    const string name;
    const shared_ptr<BSVType> interfaceType;
    const vector<shared_ptr<Stmt>> defs;
};

class PackageDefStmt : public Stmt {
public:
    PackageDefStmt(const string &name, const vector<shared_ptr<Stmt>> &package_stmts,
                   const SourcePos &sourcePos = SourcePos());

    void prettyPrint(ostream &out, int depth) override;

    shared_ptr<Stmt> lookup(const string &name);

    const vector<shared_ptr<Stmt>> stmts;

    const string name;
    map<string, shared_ptr<Stmt>> bindings;
};

class ModuleDefStmt : public Stmt {
public:
    ModuleDefStmt(const string &package, const string &name, const shared_ptr<BSVType> &interfaceType,
                  const vector<string> &params,
                  const vector<shared_ptr<BSVType>> &paramTypes,
                  const vector<shared_ptr<Stmt>> &stmts,
                  const SourcePos &sourcePos = SourcePos());

    ~ModuleDefStmt() override;

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<ModuleDefStmt> moduleDefStmt() override;

    shared_ptr<Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

public:
    const string package;
    const string name;
    const shared_ptr<BSVType> interfaceType;
    const vector<string> params;
    const vector<shared_ptr<BSVType>> paramTypes;
    const vector<shared_ptr<Stmt>> stmts;
};

class MethodDeclStmt : public Stmt {
public:
    MethodDeclStmt(const string &name, const shared_ptr<BSVType> &returnType,
                   const vector<string> &params,
                   const vector<shared_ptr<BSVType>> &paramTypes,
                   const SourcePos &sourcePos = SourcePos());

    virtual ~MethodDeclStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<MethodDeclStmt> methodDeclStmt() override;

public:
    const string name;
    const shared_ptr<BSVType> returnType;
    const vector<string> params;
    const vector<shared_ptr<BSVType>> paramTypes;
};

// ModuleInstStmt
// Represents a module-level statment that creates an instance of a module
// It's an action binding
class ModuleInstStmt : public Stmt {
public:
    ModuleInstStmt(const string &name, const shared_ptr<BSVType> &interfaceType, const shared_ptr<Expr> &rhs,
                   const SourcePos &sourcePos = SourcePos());

    ~ModuleInstStmt() override;

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<ModuleInstStmt> moduleInstStmt() override;

    shared_ptr<Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

    static shared_ptr<ModuleInstStmt>
    create(const string &name, const shared_ptr<BSVType> &interfaceType, const shared_ptr<Expr> &rhs);

public:
    const string name;
    const shared_ptr<BSVType> interfaceType;
    const shared_ptr<Expr> rhs;

};

class MethodDefStmt : public Stmt {
public:
    MethodDefStmt(const string &name,
                  const shared_ptr<BSVType> &returnType,
                  const vector<string> &params,
                  const vector<shared_ptr<BSVType>> &paramTypes,
                  const shared_ptr<Expr> &guard,
                  const vector<shared_ptr<Stmt>> &stmts,
                  const SourcePos &sourcePos = SourcePos());

    virtual ~MethodDefStmt();

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<MethodDefStmt> methodDefStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

public:
    const string name;
    const shared_ptr<BSVType> returnType;
    const vector<string> params;
    const vector<shared_ptr<BSVType>> paramTypes;
    const shared_ptr<Expr> guard;
    const vector<shared_ptr<Stmt>> stmts;
};

class FunctionDefStmt : public Stmt {
public:
    FunctionDefStmt(const string &package, const string &name, const shared_ptr<BSVType> &returnType,
                    const vector<string> &params,
                    const vector<shared_ptr<BSVType>> &paramTypes,
                    const shared_ptr<Expr> &guard,
                    const vector<shared_ptr<Stmt>> &stmts,
                    const SourcePos &sourcePos = SourcePos());

    virtual ~FunctionDefStmt();

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<FunctionDefStmt> functionDefStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

public:
    const string package;
    const string name;
    const shared_ptr<BSVType> returnType;
    const vector<string> params;
    const vector<shared_ptr<BSVType>> paramTypes;
    const shared_ptr<Expr> guard;
    const vector<shared_ptr<Stmt>> stmts;
};

class RuleDefStmt : public Stmt {
public:
    const string name;
    const shared_ptr<Expr> guard;
    const vector<shared_ptr<Stmt>> stmts;

public:
    RuleDefStmt(const string &name, const shared_ptr<Expr> &guard, const vector<shared_ptr<Stmt>> &stmts,
                const SourcePos &sourcePos = SourcePos());

    ~RuleDefStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<RuleDefStmt> ruleDefStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};


class ActionBindingStmt : public Stmt {
public:
    const shared_ptr<BSVType> bsvtype;
    const string name;
    const shared_ptr<Expr> rhs;
public:
    ActionBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name,
                      const shared_ptr<Expr> &rhs, const SourcePos &sourcePos = SourcePos());

    ~ActionBindingStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<ActionBindingStmt> actionBindingStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class VarAssignStmt : public Stmt {
public:
    const shared_ptr<LValue> lhs;
    const string op;
    const shared_ptr<Expr> rhs;
public:
    VarAssignStmt(const shared_ptr<LValue> &lhs, const string &op, const shared_ptr<Expr> &rhs,
                  const SourcePos &sourcePos = SourcePos());

    ~VarAssignStmt() override = default;

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<VarAssignStmt> varAssignStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class VarBindingStmt : public Stmt {
public:
    const string package;
    const shared_ptr<BSVType> bsvtype;
    const string name;
    const BindingType bindingType;
    const shared_ptr<Expr> rhs;
public:
    VarBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name,
                   const shared_ptr<Expr> &rhs,
                   const SourcePos &sourcePos = SourcePos());

    VarBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name, BindingType bindingType,
                   const shared_ptr<Expr> &rhs,
                   const SourcePos &sourcePos = SourcePos());

    ~VarBindingStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<VarBindingStmt> varBindingStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class PatternMatchStmt : public Stmt {
public:
    const shared_ptr<Pattern> pattern;
    const string op; // '=' or '<-'
    const shared_ptr<Expr> rhs;
public:
    PatternMatchStmt(const shared_ptr<Pattern> &pattern, const string &op,
                     const shared_ptr<Expr> &rhs, const SourcePos &sourcePos = SourcePos())
            : Stmt(PatternMatchStmtType, sourcePos), pattern(pattern), op(op), rhs(rhs) {}

    ~PatternMatchStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    shared_ptr<PatternMatchStmt> patternMatchStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class RegisterStmt : public Stmt {
public:
    const string regName;
    const shared_ptr<BSVType> elementType;
public:
    RegisterStmt(const string &regName, const shared_ptr<BSVType> &elementType,
                 const SourcePos &sourcePos = SourcePos())
            : Stmt(RegisterStmtType, sourcePos), regName(regName), elementType(elementType) {};

    ~RegisterStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<RegisterStmt> registerStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class RegReadStmt : public Stmt {
public:
    const string regName;
    const string var;
    const shared_ptr<BSVType> varType;
public:
    RegReadStmt(const string &regName, const string &var, const shared_ptr<BSVType> &varType,
                const SourcePos &sourcePos = SourcePos());

    ~RegReadStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<RegReadStmt> regReadStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

    static shared_ptr<RegReadStmt> create(const string &regName, const string &var, const shared_ptr<BSVType> &varType);

};

class RegWriteStmt : public Stmt {
public:
    const string regName;
    const shared_ptr<BSVType> elementType;
    const shared_ptr<Expr> rhs;
public:
    RegWriteStmt(const string &regName, const shared_ptr<BSVType> &elementType, const shared_ptr<Expr> &rhs,
                 const SourcePos &sourcePos = SourcePos());

    ~RegWriteStmt() override {}

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<RegWriteStmt> regWriteStmt() override;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;
};

class BlockStmt : public Stmt {
public:
    explicit BlockStmt(const vector<shared_ptr<Stmt>> &stmts, const SourcePos &sourcePos = SourcePos());

    ~BlockStmt() override;

    void prettyPrint(ostream &out, int depth = 0) override;

    virtual shared_ptr<BlockStmt> blockStmt() override;

    const vector<shared_ptr<Stmt>> stmts;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class IfStmt : public Stmt {
public:
    IfStmt(const shared_ptr<Expr> &condition, const shared_ptr<Stmt> &thenStmt,
           const shared_ptr<Stmt> &elseStmt, const SourcePos &sourcePos = SourcePos());

    ~IfStmt() override;

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<IfStmt> ifStmt() override;

    const shared_ptr<Expr> condition;
    const shared_ptr<Stmt> thenStmt;
    const shared_ptr<Stmt> elseStmt;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class ReturnStmt : public Stmt {
public:
    ReturnStmt(const shared_ptr<Expr> value, const SourcePos &sourcePos = SourcePos()) : Stmt(ReturnStmtType,
                                                                                              sourcePos),
                                                                                         value(value) {}

    ~ReturnStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<ReturnStmt> returnStmt() override;

    const shared_ptr<Expr> value;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

};

class ExprStmt : public Stmt {
public:
    ExprStmt(const shared_ptr<Expr> expr, const SourcePos &sourcePos = SourcePos())
            : Stmt(ExprStmtType, sourcePos), expr(expr) {}

    ~ExprStmt() override {}

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<ExprStmt> exprStmt() override;

    const shared_ptr<Expr> expr;

    shared_ptr<struct Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;
};

class CallStmt : public Stmt {
public:
    CallStmt(const string &name, const shared_ptr<BSVType> &interfaceType, const shared_ptr<Expr> &rhs,
             const SourcePos &sourcePos = SourcePos())
            : Stmt(CallStmtType, sourcePos), name(name), interfaceType(interfaceType), rhs(rhs) {}

    ~CallStmt() override {};

    void prettyPrint(ostream &out, int depth) override;

    virtual shared_ptr<CallStmt> callStmt() override;

    shared_ptr<Stmt> rename(string prefix, shared_ptr<LexicalScope> &parentScope) override;

public:
    const string name;
    const shared_ptr<BSVType> interfaceType;
    const shared_ptr<Expr> rhs;

};