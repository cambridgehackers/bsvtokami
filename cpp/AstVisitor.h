//
// Created by Jamey Hicks on 1/27/20.
//

#ifndef BSV_PARSER_ASTVISITOR_H
#define BSV_PARSER_ASTVISITOR_H

#include "Stmt.h"
#include "Expr.h"
#include "BSVType.h"

class AstVisitor {
public:
    AstVisitor() {}
    virtual ~AstVisitor() {}

    void visit(const shared_ptr<Stmt> &stmt);

    void visit(const shared_ptr<Expr> &expr);

    void visit(const shared_ptr<BSVType> &bsvtype);

    virtual void visitModuleDef(const shared_ptr<ModuleDefStmt> &sharedPtr);

    virtual void visitActionBindingStmt(const shared_ptr<ActionBindingStmt> &sharedPtr);

    virtual void visitBlockStmt(const shared_ptr<BlockStmt> sharedPtr);

    virtual void visitCallStmt(const shared_ptr<CallStmt> sharedPtr);

    virtual void visitExprStmt(const shared_ptr<ExprStmt> sharedPtr);

    virtual void visitFunctionDefStmt(const shared_ptr<FunctionDefStmt> sharedPtr);

    virtual void visitInterfaceDeclStmt(const shared_ptr<InterfaceDeclStmt> sharedPtr);

    virtual void visitIfStmt(const shared_ptr<IfStmt> sharedPtr);

    virtual void visitImportStmt(const shared_ptr<ImportStmt> sharedPtr);

    virtual void visitMethodDeclStmt(const shared_ptr<MethodDeclStmt> sharedPtr);

    virtual void visitModuleInstStmt(const shared_ptr<ModuleInstStmt> sharedPtr);

    virtual void visitPackageDefStmt(const shared_ptr<PackageDefStmt> sharedPtr);

    virtual void visitPatternMatchStmt(const shared_ptr<PatternMatchStmt> sharedPtr);

    virtual void visitRegisterStmt(const shared_ptr<RegisterStmt> sharedPtr);

    virtual void visitRegReadStmt(const shared_ptr<RegReadStmt> sharedPtr);

    virtual void visitRegWriteStmt(const shared_ptr<RegWriteStmt> sharedPtr);

    virtual void visitReturnStmt(const shared_ptr<ReturnStmt> sharedPtr);

    virtual void visitTypedefEnumStmt(const shared_ptr<TypedefEnumStmt> sharedPtr);

    virtual void visitTypedefStructStmt(const shared_ptr<TypedefStructStmt> sharedPtr);

    virtual void visitTypedefSynonymStmt(const shared_ptr<TypedefSynonymStmt> sharedPtr);

    virtual void visitVarBindingStmt(const shared_ptr<VarBindingStmt> sharedPtr);

    virtual void visitVarAssignStmt(const shared_ptr<VarAssignStmt> sharedPtr);

    virtual void visitRuleDefStmt(const shared_ptr<RuleDefStmt> sharedPtr);

    virtual void visitArraySubExpr(const shared_ptr<ArraySubExpr> sharedPtr);

    virtual void visitBitConcatExpr(const shared_ptr<BitConcatExpr> sharedPtr);

    virtual void visitBitSelExpr(const shared_ptr<BitSelExpr> sharedPtr);

    virtual void visitVarExpr(const shared_ptr<VarExpr> sharedPtr);

    virtual void visitIntConst(const shared_ptr<IntConst> sharedPtr);

    virtual void visitInterfaceExpr(const shared_ptr<InterfaceExpr> sharedPtr);

    virtual void visitSubinterfaceExpr(const shared_ptr<SubinterfaceExpr> sharedPtr);

    virtual void visitStringConst(const shared_ptr<StringConst> sharedPtr);

    virtual void visitOperatorExpr(const shared_ptr<OperatorExpr> sharedPtr);

    virtual void visitCallExpr(const shared_ptr<CallExpr> sharedPtr);

    virtual void visitFieldExpr(const shared_ptr<FieldExpr> sharedPtr);

    virtual void visitCondExpr(const shared_ptr<CondExpr> sharedPtr);

    virtual void visitCaseExpr(const shared_ptr<CaseExpr> sharedPtr);

    virtual void visitEnumUnionStructExpr(const shared_ptr<EnumUnionStructExpr> sharedPtr);

    virtual void visitMatchesExpr(const shared_ptr<MatchesExpr> sharedPtr);

    virtual void visitMethodExpr(const shared_ptr<MethodExpr> sharedPtr);

    virtual void visitValueofExpr(const shared_ptr<ValueofExpr> sharedPtr);
};


#endif //BSV_PARSER_ASTVISITOR_H
