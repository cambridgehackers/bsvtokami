//
// Created by Jamey Hicks on 8/11/20.
//

#pragma once

#include <string>
#include "AstVisitor.h"
#include "source_pos.pb.h"
#include "expr.pb.h"
#include "pattern.pb.h"
#include "lvalue.pb.h"
#include "stmt.pb.h"

class AstWriter {
private:
    bsvproto::PackageDef packagedef_proto;
public:
    AstWriter();

    virtual ~AstWriter() noexcept;

    bool writeAst(std::string filename);

    void visit(const shared_ptr<Stmt> &stmt, bsvproto::Stmt *stmt_proto = nullptr);

    void visit(const shared_ptr<Expr> &expr, bsvproto::Expr *expr_proto);

    void visit(const shared_ptr<BSVType> &bsvtype, bsvproto::BSVType *bsvtype_proto);

    void visit(const shared_ptr<LValue> &lvalue, bsvproto::LValue *lvalue_proto);

    void visit(const shared_ptr<Pattern> &pattern, bsvproto::Pattern *pattern_proto);

    void visit(const SourcePos &sourcePos, bsvproto::SourcePos *sourcePos_proto);


    void visitPackageDefStmt(const shared_ptr<PackageDefStmt> packageDef);

    static bsvproto::SourcePos *newSourcePos(const SourcePos &sourcePos);

    void visitActionBindingStmt(shared_ptr<ActionBindingStmt> stmt, bsvproto::Stmt *stmt_proto);

    void visitBlockStmt(shared_ptr<BlockStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitCallStmt(shared_ptr<CallStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitExprStmt(shared_ptr<ExprStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitModuleDefStmt(const shared_ptr<ModuleDefStmt> &moduleDef, bsvproto::Stmt *stmt_proto);

    void visitFunctionDefStmt(shared_ptr<FunctionDefStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitInterfaceDeclStmt(shared_ptr<InterfaceDeclStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitInterfaceDefStmt(shared_ptr<InterfaceDefStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitIfStmt(shared_ptr<IfStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitImportStmt(shared_ptr<ImportStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitMethodDeclStmt(shared_ptr<MethodDeclStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitMethodDefStmt(shared_ptr<MethodDefStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitModuleInstStmt(shared_ptr<ModuleInstStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitPatternMatchStmt(shared_ptr<PatternMatchStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitRegisterStmt(shared_ptr<RegisterStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitRegReadStmt(shared_ptr<RegReadStmt> sharedPtr, bsvproto::Stmt *pStmt);

    void visitRegWriteStmt(shared_ptr<RegWriteStmt> regWriteStmt, bsvproto::Stmt *stmt_proto);

    void visitReturnStmt(shared_ptr<ReturnStmt> returnStmt, bsvproto::Stmt *stmt_proto);

    void visitTypedefEnumStmt(shared_ptr<TypedefEnumStmt> typedefEnumStmt, bsvproto::Stmt *stmt_proto);

    void visitTypedefStructStmt(shared_ptr<TypedefStructStmt> typedefStructStmt, bsvproto::Stmt *stmt_proto);

    void visitTypedefSynonymStmt(shared_ptr<TypedefSynonymStmt> typedefSynonymStmt, bsvproto::Stmt *stmt_proto);

    void visitVarBindingStmt(shared_ptr<VarBindingStmt> varBindingStmt, bsvproto::Stmt *stmt_proto);

    void visitVarAssignStmt(shared_ptr<VarAssignStmt> varAssignStmt, bsvproto::Stmt *stmt_proto);

    void visitRuleDefStmt(shared_ptr<RuleDefStmt> ruleDefStmt, bsvproto::Stmt *stmt_proto);

    void visitArraySubExpr(shared_ptr<ArraySubExpr> arraySubExprType, bsvproto::Expr *expr_proto);

    void visitBitConcatExpr(shared_ptr<BitConcatExpr> bitConcatExprType, bsvproto::Expr *expr_proto);

    void visitBitSelExpr(shared_ptr<BitSelExpr> bitSelExprType, bsvproto::Expr *expr_proto);

    void visitVarExpr(shared_ptr<VarExpr> varExprType, bsvproto::Expr *expr_proto);

    void visitIntConst(shared_ptr<IntConst> intConstType, bsvproto::Expr *expr_proto);

    void visitInterfaceExpr(shared_ptr<InterfaceExpr> interfaceExprType, bsvproto::Expr *expr_proto);

    void visitSubinterfaceExpr(shared_ptr<SubinterfaceExpr> subinterfaceExprType, bsvproto::Expr *expr_proto);

    void visitStringConst(shared_ptr<StringConst> stringConstType, bsvproto::Expr *expr_proto);

    void visitOperatorExpr(shared_ptr<OperatorExpr> operatorExprType, bsvproto::Expr *expr_proto);

    void visitCallExpr(shared_ptr<CallExpr> callExprType, bsvproto::Expr *expr_proto);

    void visitFieldExpr(shared_ptr<FieldExpr> fieldExprType, bsvproto::Expr *expr_proto);

    void visitCondExpr(shared_ptr<CondExpr> condExprType, bsvproto::Expr *expr_proto);

    void visitCaseExpr(shared_ptr<CaseExpr> caseExprType, bsvproto::Expr *expr_proto);

    void visitEnumUnionStructExpr(shared_ptr<EnumUnionStructExpr> enumUnionStructExprType, bsvproto::Expr *expr_proto);

    void visitMatchesExpr(shared_ptr<MatchesExpr> matchesExprType, bsvproto::Expr *expr_proto);

    void visitMethodExpr(shared_ptr<MethodExpr> methodExprType, bsvproto::Expr *expr_proto);

    void visitValueofExpr(shared_ptr<ValueofExpr> valueofExprType, bsvproto::Expr *expr_proto);

    void visitIntPattern(const shared_ptr<IntPattern> &intPattern, bsvproto::Pattern *pattern_pro);

    void visitTaggedPattern(const shared_ptr<TaggedPattern> &taggedPattern, bsvproto::Pattern *pattern_proto);

    void
    visitTuplePattern(const shared_ptr<TuplePattern> &tuplePattern, bsvproto::Pattern *pattern_pro);

    void visitVarPattern(const shared_ptr<VarPattern> &varPattern, bsvproto::Pattern *pattern_pro);

    void visitWildcardPattern(const shared_ptr<WildcardPattern> &wildcardPattern,
                              bsvproto::Pattern *pattern_pro);

    void visitArraySubLValue(const shared_ptr<ArraySubLValue> &arraySubLValue, bsvproto::LValue *lvalue_proto);

    void visitFieldLValue(const shared_ptr<FieldLValue> &fieldLValue, bsvproto::LValue *lvalue_proto);

    void visitVarLValue(const shared_ptr<VarLValue> &varLValue, bsvproto::LValue *lvalue_proto);

    void visitRangeSelLValue(const shared_ptr<RangeSelLValue> &rangeSelLValue, bsvproto::LValue *lvalue_proto);

};
