#pragma once

#include <string>
#include <vector>
#include <memory>

#include "BSVType.h"
#include "Expr.h"

enum StmtType {
    InvalidStmtType,
    ActionBindingStmtType,
    BlockStmtType,
    ExprStmtType,
    InterfaceDeclStmtType,
    IfStmtType,
    ImportStmtType,
    MethodDeclStmtType,
    MethodDefStmtType,
    ModuleDefStmtType,
    RetStmtType,
    TypedefStructStmtType,
    TypedefSynonymStmtType,
    VarBindingStmtType,
    RuleDefStmtType,
    RegWriteStmtType
};

class Stmt {
protected:
    const StmtType stmtType;

public:
    Stmt(StmtType stmtType);

    virtual ~Stmt() {}

    virtual void prettyPrint(int depth = 0) = 0;
};

class ImportStmt : public Stmt {
public:
    explicit ImportStmt(const std::string name);
    ~ImportStmt() override {}
    void prettyPrint(int depth = 0) override ;
private:
    std::string name;
};

class TypedefSynonymStmt : public Stmt {
public:
    TypedefSynonymStmt(const std::shared_ptr<BSVType> &typedeftype, const std::shared_ptr<BSVType> &type);
    ~TypedefSynonymStmt() override {}
    void prettyPrint(int depth = 0) override ;
private:
    std::shared_ptr<BSVType> typedeftype; // type being defined
    std::shared_ptr<BSVType> type;
};

class TypedefStructStmt : public Stmt {
public:
    TypedefStructStmt(const std::string &name, const std::shared_ptr<BSVType> &structType,
                   const std::vector<std::string> &members,
                   const std::vector<std::shared_ptr<BSVType>> &memberTypes);

    virtual ~TypedefStructStmt() override {}

    void prettyPrint(int depth) override;

private:
    std::string name;
    std::shared_ptr<BSVType> structType;
    std::vector<std::string> members;
    std::vector<std::shared_ptr<BSVType>> memberTypes;
};

class InterfaceDeclStmt : public Stmt {
public:
    InterfaceDeclStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                  const std::vector<std::shared_ptr<Stmt>> &decls);

    ~InterfaceDeclStmt() override {}

    void prettyPrint(int depth) override;

private:
    std::string name;
    std::shared_ptr<BSVType> interfaceType;
    std::vector<std::shared_ptr<Stmt>> decls;
};

class ModuleDefStmt : public Stmt {
public:
    ModuleDefStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                  const std::vector<std::string> &params,
                  const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                  const std::vector<std::shared_ptr<Stmt>> &stmts);

    ~ModuleDefStmt() override;

    void prettyPrint(int depth) override;

private:
    std::string name;
    std::shared_ptr<BSVType> interfaceType;
    std::vector<std::string> params;
    std::vector<std::shared_ptr<BSVType>> paramTypes;
    std::vector<std::shared_ptr<Stmt>> stmts;
};

class MethodDeclStmt : public Stmt {
public:
    MethodDeclStmt(const std::string &name, const std::shared_ptr<BSVType> &returnType,
                  const std::vector<std::string> &params,
                  const std::vector<std::shared_ptr<BSVType>> &paramTypes);

    virtual ~MethodDeclStmt() override {}

    void prettyPrint(int depth) override;

private:
    std::string name;
    std::shared_ptr<BSVType> returnType;
    std::vector<std::string> params;
    std::vector<std::shared_ptr<BSVType>> paramTypes;
};

class MethodDefStmt : public Stmt {
public:
    MethodDefStmt(const std::string &name, const std::shared_ptr<BSVType> &returnType,
                  const std::vector<std::string> &params,
                  const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                  const std::shared_ptr<Expr> &guard,
                  const std::vector<std::shared_ptr<Stmt>> &stmts);

    virtual ~MethodDefStmt();

    void prettyPrint(int depth) override;

private:
    std::string name;
    std::shared_ptr<BSVType> returnType;
    std::vector<std::string> params;
    std::vector<std::shared_ptr<BSVType>> paramTypes;
    std::shared_ptr<Expr> guard;
    std::vector<std::shared_ptr<Stmt>> stmts;
};

class RuleDefStmt : public Stmt {
    std::string name;
    std::shared_ptr<Expr> guard;
    std::vector<std::shared_ptr<Stmt>> stmts;
public:
    RuleDefStmt(std::string name, std::shared_ptr<Expr> guard);

    ~RuleDefStmt() override {}

    void addStmt(std::shared_ptr<Stmt> stmt) {
        stmts.push_back(stmt);
    }

    void prettyPrint(int depth = 0) override;
};


class ActionBindingStmt : public Stmt {
    std::shared_ptr<BSVType> bsvtype;
    std::string name;
    std::shared_ptr<Expr> rhs;
public:
    ActionBindingStmt(const std::shared_ptr<BSVType> &bsvtype, const std::string &name,
                   const std::shared_ptr<Expr> &rhs);

    ~ActionBindingStmt() override {}

    void prettyPrint(int depth = 0) override;

};

class VarBindingStmt : public Stmt {
    std::shared_ptr<BSVType> bsvtype;
    std::string name;
    std::shared_ptr<Expr> rhs;
public:
    VarBindingStmt(const std::shared_ptr<BSVType> &bsvtype, const std::string &name,
                   const std::shared_ptr<Expr> &rhs);

    ~VarBindingStmt() override {}

    void prettyPrint(int depth = 0) override;

};

class RegWriteStmt : public Stmt {
    std::string regName;
    std::shared_ptr<Expr> rhs;
public:
    RegWriteStmt(std::string regName, std::shared_ptr<Expr> rhs);

    ~RegWriteStmt() override {}

    void prettyPrint(int depth = 0) override;
};

class BlockStmt : public Stmt {
public:
    explicit BlockStmt(std::vector<std::shared_ptr<Stmt>> stmts);

    ~BlockStmt() override;

    void prettyPrint(int depth = 0) override;
private:
    std::vector<std::shared_ptr<Stmt>> stmts;
};

class IfStmt : public Stmt {
public:
    IfStmt(const std::shared_ptr<Expr> &condition, const std::shared_ptr<Stmt> &thenStmt,
           const std::shared_ptr<Stmt> &elseStmt);

    ~IfStmt() override;

    void prettyPrint(int depth) override;

private:
    std::shared_ptr<Expr> condition;
    std::shared_ptr<Stmt> thenStmt;
    std::shared_ptr<Stmt> elseStmt;
};

class RetStmt : public Stmt {
public:
    RetStmt(const std::shared_ptr<Expr> value) : Stmt(RetStmtType), value(value) {}
    ~RetStmt() override {}
    void prettyPrint(int depth) override;
private:
    std::shared_ptr<Expr> value;
};

class ExprStmt : public Stmt {
public:
    ExprStmt(const std::shared_ptr<Expr> value) : Stmt(ExprStmtType), value(value) {}
    ~ExprStmt() override {}
    void prettyPrint(int depth) override;
private:
    std::shared_ptr<Expr> value;
};
