
#include <iostream>

using namespace std;

#include "Stmt.h"

void indent(ostream &s, int depth) {
    for (int i = 0; i < depth*4; i++)
        s << " ";
}

Stmt::Stmt(StmtType stmtType, const SourcePos &sourcePos)
        : stmtType(stmtType), sourcePos(sourcePos) {
}

shared_ptr<Stmt> Stmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    return shared_ptr<Stmt>();
}

RuleDefStmt::RuleDefStmt(const string &name, const shared_ptr<Expr> &guard, const vector<shared_ptr<Stmt>> &stmts, const SourcePos &sourcePos)
        : Stmt(RuleDefStmtType, sourcePos), name(name), guard(guard), stmts(stmts) {
}

void RuleDefStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "rule " << name;
    if (guard) {
        out << " when (";
        guard->prettyPrint(out, 0);
        out << ")";
    }
    out << ";" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt(stmts.at(i));
        if (stmt)
            stmt->prettyPrint(out, depth + 1);
    }
    indent(out, 4 * depth);
    out << "endrule //" << name << endl;
}

shared_ptr<RuleDefStmt> RuleDefStmt::ruleDefStmt() {
    return static_pointer_cast<RuleDefStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> RuleDefStmt::rename(string prefix, shared_ptr<LexicalScope> &parentScope) {
    shared_ptr<LexicalScope> scope(make_shared<LexicalScope>(name, parentScope));
    shared_ptr<Expr> renamedGuard;
    if (guard)
        renamedGuard = guard->rename(prefix, parentScope);
    vector<shared_ptr<Stmt>> renamedStmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        renamedStmts.push_back(stmts[i]->rename(prefix, scope));
    }
    return shared_ptr<Stmt>(new RuleDefStmt(prefix + name, renamedGuard, renamedStmts));
}

void RegisterStmt::prettyPrint(ostream &out, int depth) {
    out << "Register" << regName << " : ";
    elementType->prettyPrint(out, depth);
    out << ";" << endl;
}

shared_ptr<RegisterStmt> RegisterStmt::registerStmt() {
    return static_pointer_cast<RegisterStmt, Stmt>(shared_from_this());
}

shared_ptr<struct Stmt> RegisterStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    return make_shared<RegisterStmt>(regName, elementType);
}

RegReadStmt::RegReadStmt(const string &regName, const string &var, const shared_ptr<BSVType> &varType, const SourcePos &sourcePos)
        : Stmt(RegReadStmtType, sourcePos), regName(regName), var(var), varType(varType) {
}

void RegReadStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << var << " : ";
    varType->prettyPrint(out, depth);
    out << " = (* reg read *)" << regName << ";" << endl;
}

shared_ptr<RegReadStmt> RegReadStmt::regReadStmt() {
    return static_pointer_cast<RegReadStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> RegReadStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    string renamedRegName = regName;
    shared_ptr<Declaration> decl = scope->lookup(regName);
    if (decl) {
        renamedRegName = decl->name;
    }
    shared_ptr<Expr> renamedRHS;
    //FIXME renamed var
    return RegReadStmt::create(renamedRegName, var, varType);
}

shared_ptr<RegReadStmt> RegReadStmt::create(const string &regName, const string &var, const shared_ptr<BSVType> &varType) {
    return make_shared<RegReadStmt>(regName, var, varType);
}

RegWriteStmt::RegWriteStmt(const string &regName, const shared_ptr<BSVType> &elementType, const shared_ptr<Expr> &rhs, const SourcePos &sourcePos)
        : Stmt(RegWriteStmtType, sourcePos), regName(regName), elementType(elementType), rhs(rhs) {
}

void RegWriteStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << regName << " <= ";
    if (rhs)
        rhs->prettyPrint(out, depth + 1);
    else
        out << "no_rhs";
    out << ";" << endl;
}

shared_ptr<RegWriteStmt> RegWriteStmt::regWriteStmt() {
    return static_pointer_cast<RegWriteStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> RegWriteStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    string renamedRegName = regName;
    shared_ptr<Declaration> decl = scope->lookup(regName);
    if (decl) {
        renamedRegName = decl->name;
    }
    shared_ptr<Expr> renamedRHS;
    if (rhs)
        renamedRHS = rhs->rename(prefix, scope);
    return make_shared<RegWriteStmt>(renamedRegName, elementType, renamedRHS);
}

ActionBindingStmt::ActionBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name,
                                     const shared_ptr<Expr> &rhs, const SourcePos &sourcePos)
        : Stmt(ActionBindingStmtType, sourcePos), bsvtype(bsvtype), name(name), rhs(rhs) {

}

void ActionBindingStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    bsvtype->prettyPrint(out, 0);
    out << " " << name << " <- ";
    rhs->prettyPrint(out, depth + 1);
    out << ";" << endl;

}

shared_ptr<ActionBindingStmt>
ActionBindingStmt::actionBindingStmt() { return static_pointer_cast<ActionBindingStmt, Stmt>(shared_from_this()); }


shared_ptr<Stmt> ActionBindingStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    string renamedVar = prefix + name;
    shared_ptr<Expr> renamedRHS;
    cerr << "Renaming action binding" << endl;
    rhs->prettyPrint(cerr, 4);
    if (rhs)
        renamedRHS = rhs->rename(prefix, scope);
    scope->bind(name, make_shared<Declaration>(renamedVar, bsvtype));
    return shared_ptr<Stmt>(new ActionBindingStmt(bsvtype, renamedVar, renamedRHS));
}

void PatternMatchStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "{";
    pattern->prettyPrint(out, depth+1);
    out << "}";
    if (rhs) {
        out << op;
        rhs->prettyPrint(out, depth + 1);
    }
    out << ";" << endl;
}

shared_ptr<PatternMatchStmt> PatternMatchStmt::patternMatchStmt() {
    return static_pointer_cast<PatternMatchStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> PatternMatchStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    shared_ptr<Expr> renamedRHS;
    if (rhs)
        renamedRHS = rhs->rename(prefix, scope);
    //scope->bind(name, renamedVar);
    return make_shared<PatternMatchStmt>(pattern, op, renamedRHS);
}

VarBindingStmt::VarBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name,
                               const shared_ptr<Expr> &rhs, const SourcePos &sourcePos)
        : Stmt(VarBindingStmtType, sourcePos), bsvtype(bsvtype), name(name), bindingType(LocalBindingType), rhs(rhs) {

}

VarBindingStmt::VarBindingStmt(const shared_ptr<BSVType> &bsvtype, const string &name, BindingType bindingType,
                               const shared_ptr<Expr> &rhs, const SourcePos &sourcePos)
        : Stmt(VarBindingStmtType, sourcePos), bsvtype(bsvtype), name(name), bindingType(bindingType), rhs(rhs) {

}

void VarBindingStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    if (bsvtype) bsvtype->prettyPrint(out, 0);
    out << " " << name;
    if (rhs) {
        out << " = ";
        rhs->prettyPrint(out, depth + 1);
    }
    out << ";" << endl;
}

shared_ptr<VarBindingStmt> VarBindingStmt::varBindingStmt() {
    return static_pointer_cast<VarBindingStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> VarBindingStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    string renamedVar = prefix + name;
    shared_ptr<Expr> renamedRHS;
    if (rhs)
        renamedRHS = rhs->rename(prefix, scope);
    scope->bind(name, make_shared<Declaration>(renamedVar, bsvtype, bindingType));
    return shared_ptr<Stmt>(new VarBindingStmt(bsvtype, renamedVar, renamedRHS));
}

VarAssignStmt::VarAssignStmt(const shared_ptr<LValue> &lhs, const string &op, const shared_ptr<Expr> &rhs, const SourcePos &sourcePos)
        : Stmt(VarAssignStmtType, sourcePos), lhs(lhs), op(op), rhs(rhs) {

}

void VarAssignStmt::prettyPrint(ostream &out, int depth)
{
    indent(out, 4 * depth);
    lhs->prettyPrint(out, depth);
    out << " " << op << " ";
    rhs->prettyPrint(out, depth + 1);
    out << endl;
}

shared_ptr<VarAssignStmt> VarAssignStmt::varAssignStmt() {
    return static_pointer_cast<VarAssignStmt, Stmt>(shared_from_this());
}

shared_ptr<struct Stmt> VarAssignStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    shared_ptr<LValue> newLHS; //FIXME
    return shared_ptr<Stmt>(new VarAssignStmt(newLHS, op, rhs->rename(prefix, scope)));
}


FunctionDefStmt::FunctionDefStmt(const string &name, const shared_ptr<BSVType> &returnType,
                                 const std::vector<std::string> &params,
                                 const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                                 const shared_ptr<Expr> &guard,
                                 const vector<std::shared_ptr<Stmt>> &stmts,
                                 const SourcePos &sourcePos)
        : Stmt(FunctionDefStmtType, sourcePos), name(name), returnType(returnType),
          params(params), paramTypes(paramTypes),
          guard(guard), stmts(stmts) {}

FunctionDefStmt::~FunctionDefStmt() {

}

void FunctionDefStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "function ";
    returnType->prettyPrint(out, depth + 1);
    out << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            out << ", ";
        paramTypes[i]->prettyPrint(out, depth + 1);
        out << " " << params[i];
    }
    out << ");" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        stmts.at(i)->prettyPrint(out, depth + 1);
    }
    indent(out, 4 * depth);
    out << "endfunction" << endl;
}

shared_ptr<FunctionDefStmt> FunctionDefStmt::functionDefStmt(){
    return static_pointer_cast<FunctionDefStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> FunctionDefStmt::rename(string prefix, shared_ptr<LexicalScope> &parentScope) {
    shared_ptr<LexicalScope> scope(make_shared<LexicalScope>(name, parentScope));
    shared_ptr<Expr> renamedGuard;
    if (guard)
        renamedGuard = guard->rename(prefix, parentScope);
    vector<shared_ptr<Stmt>> renamedStmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        renamedStmts.push_back(stmts[i]->rename(prefix, scope));
    }
    return shared_ptr<Stmt>(new FunctionDefStmt(name, returnType, params, paramTypes, renamedGuard, renamedStmts));
}

MethodDeclStmt::MethodDeclStmt(const string &name, const shared_ptr<BSVType> &returnType,
                               const std::vector<std::string> &params,
                               const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                               const SourcePos &sourcePos)
        : Stmt(MethodDeclStmtType, sourcePos), name(name), returnType(returnType),
          params(params), paramTypes(paramTypes) {}

void MethodDeclStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "method ";
    returnType->prettyPrint(out, depth + 1);
    out << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            out << ", ";
        paramTypes[i]->prettyPrint(out, depth + 1);
        out << " " << params[i];
    }
    out << ");" << endl;
    indent(out, 4 * depth);
    out << "endmethod" << endl;
}

shared_ptr<MethodDeclStmt> MethodDeclStmt::methodDeclStmt(){
    return static_pointer_cast<MethodDeclStmt, Stmt>(shared_from_this());
}


MethodDefStmt::MethodDefStmt(const string &name, const shared_ptr<BSVType> &returnType,
                             const std::vector<std::string> &params,
                             const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                             const shared_ptr<Expr> &guard,
                             const vector<std::shared_ptr<Stmt>> &stmts,
                             const SourcePos &sourcePos)
        : Stmt(MethodDefStmtType, sourcePos), name(name), returnType(returnType),
          params(params), paramTypes(paramTypes),
          guard(guard), stmts(stmts) {}

MethodDefStmt::~MethodDefStmt() {

}

void MethodDefStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "method ";
    returnType->prettyPrint(out, depth + 1);
    out << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            out << ", ";
        paramTypes[i]->prettyPrint(out, depth + 1);
        out << " " << params[i];
    }
    out << ");" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        stmts.at(i)->prettyPrint(out, depth + 1);
    }
    indent(out, 4 * depth);
    out << "endmethod" << endl;
}

shared_ptr<MethodDefStmt> MethodDefStmt::methodDefStmt() {
    return static_pointer_cast<MethodDefStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> MethodDefStmt::rename(string prefix, shared_ptr<LexicalScope> &parentScope) {
    shared_ptr<LexicalScope> scope(make_shared<LexicalScope>(name, parentScope));
    shared_ptr<Expr> renamedGuard;
    if (guard)
        renamedGuard = guard->rename(prefix, parentScope);
    vector<shared_ptr<Stmt>> renamedStmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        renamedStmts.push_back(stmts[i]->rename(prefix, scope));
    }
    return shared_ptr<Stmt>(new MethodDefStmt(name, returnType, params, paramTypes, renamedGuard, renamedStmts));
}

ModuleDefStmt::ModuleDefStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                             const std::vector<std::string> &params,
                             const std::vector<std::shared_ptr<BSVType>> &paramTypes,
                             const std::vector<std::shared_ptr<Stmt>> &stmts,
                             const SourcePos &sourcePos)
        : Stmt(ModuleDefStmtType, sourcePos), name(name),
          params(params), paramTypes(paramTypes),
          interfaceType(interfaceType), stmts(stmts) {

}

ModuleDefStmt::~ModuleDefStmt() {

}

void ModuleDefStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "module ";
    interfaceType->prettyPrint(out, depth + 1);
    out << " " << name << "(";
    for (size_t i = 0; i < params.size(); i++) {
        if (i > 0)
            out << ", ";
        paramTypes[i]->prettyPrint(out, depth + 1);
        out << " " << params[i];
    }
    out << ");" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        if (stmts.at(i))
            stmts.at(i)->prettyPrint(out, depth + 1);
        else
            out << "Empty stmt ..." << endl;
    }
    indent(out, 4 * depth);
    out << "endmodule" << endl;
}

shared_ptr<ModuleDefStmt> ModuleDefStmt::moduleDefStmt() {
    return static_pointer_cast<ModuleDefStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> ModuleDefStmt::rename(string prefix, shared_ptr<LexicalScope> &parentScope) {
    shared_ptr<LexicalScope> scope(make_shared<LexicalScope>(name, parentScope));
    vector<string> renamedParams;
    vector<shared_ptr<Stmt>> renamedStmts;
    //FIXME: rename module?
    for (size_t i = 0; i < params.size(); i++) {
        string renamedParam(prefix + params[i]);
        renamedParams.push_back(renamedParam);
        scope->bind(params[i], make_shared<Declaration>(renamedParam, paramTypes[i], ModuleParamBindingType));
    }
    for (size_t i = 0; i < stmts.size(); i++) {
        cerr << "renaming stmt" << endl;
        stmts[i]->prettyPrint(cerr, 0);
        renamedStmts.push_back(stmts[i]->rename(prefix, scope));
    }
    return shared_ptr<Stmt>(new ModuleDefStmt(name, interfaceType, renamedParams, paramTypes, renamedStmts));
}

ModuleInstStmt::ModuleInstStmt(const string &name, const shared_ptr<BSVType> &interfaceType,
                               const shared_ptr<Expr> &rhs, const SourcePos &sourcePos)
        : Stmt(ModuleInstStmtType, sourcePos), name(name), interfaceType(interfaceType), rhs(rhs) {
}

ModuleInstStmt::~ModuleInstStmt() {}

void ModuleInstStmt::prettyPrint(ostream &out, int depth) {
    indent(out, depth);
    interfaceType->prettyPrint(out, depth+1);
    out << " " << name << " <- ";
    rhs->prettyPrint(out, depth);
    out << ";" << endl;
}

shared_ptr<ModuleInstStmt> ModuleInstStmt::moduleInstStmt() {
    return static_pointer_cast<ModuleInstStmt, Stmt>(shared_from_this());
}

shared_ptr<Stmt> ModuleInstStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    //FIXME:
    return create(name, interfaceType, rhs->rename(prefix, scope));
}

shared_ptr<ModuleInstStmt> ModuleInstStmt::create(const string &name, const shared_ptr<BSVType> &interfaceType, const shared_ptr<Expr> &rhs) {
    return shared_ptr<ModuleInstStmt>(new ModuleInstStmt(name, interfaceType, rhs));
}


IfStmt::IfStmt(const shared_ptr<Expr> &condition, const shared_ptr<Stmt> &thenStmt,
               const shared_ptr<Stmt> &elseStmt, const SourcePos &sourcePos) : Stmt(IfStmtType, sourcePos),
                                                                               condition(condition), thenStmt(thenStmt),
                                                                               elseStmt(elseStmt) {}

IfStmt::~IfStmt() {

}

void IfStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "if (";
    condition->prettyPrint(out);
    out << ") ";
    thenStmt->prettyPrint(out, depth + 1);
    if (elseStmt) {
        indent(out, 4 * depth);
        out << "else ";
        elseStmt->prettyPrint(out, depth + 1);
    }
    out << endl;
}

shared_ptr<IfStmt> IfStmt::ifStmt() { return static_pointer_cast<IfStmt, Stmt>(shared_from_this()); }

shared_ptr<struct Stmt> IfStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    if (elseStmt)
        return shared_ptr<Stmt>(new IfStmt(condition->rename(prefix, scope),
                                           thenStmt->rename(prefix, scope),
                                           elseStmt->rename(prefix, scope)));
    else
        return shared_ptr<Stmt>(new IfStmt(condition->rename(prefix, scope),
                                           thenStmt->rename(prefix, scope),
                                           shared_ptr<Stmt>()));
}

BlockStmt::BlockStmt(const std::vector<std::shared_ptr<Stmt>> &stmts, const SourcePos &sourcePos)
        : Stmt(BlockStmtType, sourcePos), stmts(stmts) {}

BlockStmt::~BlockStmt() {}

void BlockStmt::prettyPrint(ostream &out, int depth) {
    out << "begin" << endl;
    for (size_t i = 0; i < stmts.size(); i++) {
        if (stmts.at(i))
            stmts.at(i)->prettyPrint(out, depth + 1);
        else
            out << "emptystmt:" << to_string(i) << endl;
    }
    indent(out, 4 * depth);
    out << "end" << endl;
}

shared_ptr<BlockStmt> BlockStmt::blockStmt() { return static_pointer_cast<BlockStmt, Stmt>(shared_from_this()); }

shared_ptr<struct Stmt> BlockStmt::rename(string prefix, shared_ptr<LexicalScope> &parentScope) {
    shared_ptr<LexicalScope> scope(make_shared<LexicalScope>("block", parentScope));
    vector<shared_ptr<Stmt>> renamedStmts;
    for (size_t i = 0; i < stmts.size(); i++) {
        renamedStmts.push_back(stmts[i]->rename(prefix, scope));
    }
    return shared_ptr<Stmt>(new BlockStmt(renamedStmts));
}

void CallStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "Call" << name << " : ";
    interfaceType->prettyPrint(out, depth);
    out << " <- ";
    rhs->prettyPrint(out, depth + 1);
    out << endl;
}

shared_ptr<CallStmt> CallStmt::callStmt() { return static_pointer_cast<CallStmt, Stmt>(shared_from_this()); }

shared_ptr<Stmt> CallStmt::rename(string prefix, shared_ptr<LexicalScope> &scope)
{
    cerr << "FIXME: unhandled CallStmt::rename" << endl;
    return make_shared<CallStmt>(name, interfaceType, rhs);
}

void ReturnStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "return ";
    value->prettyPrint(out, depth);
    out << ";" << endl;
}

shared_ptr<ReturnStmt> ReturnStmt::returnStmt() { return static_pointer_cast<ReturnStmt, Stmt>(shared_from_this()); }

shared_ptr<struct Stmt> ReturnStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    return shared_ptr<Stmt>(new ReturnStmt(value->rename(prefix, scope)));
}

void ExprStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    expr->prettyPrint(out, depth);
    out << ";" << endl;
}

shared_ptr<ExprStmt> ExprStmt::exprStmt() { return static_pointer_cast<ExprStmt, Stmt>(shared_from_this()); }

shared_ptr<struct Stmt> ExprStmt::rename(string prefix, shared_ptr<LexicalScope> &scope) {
    return shared_ptr<Stmt>(new ExprStmt(expr->rename(prefix, scope)));
}

ImportStmt::ImportStmt(const std::string &name, const SourcePos &sourcePos) : Stmt(ImportStmtType, sourcePos), name(name) {
}

void ImportStmt::prettyPrint(ostream &out, int depth) {
    out << "import " << name << " :: *;" << endl;
}

shared_ptr<ImportStmt> ImportStmt::importStmt() { return static_pointer_cast<ImportStmt, Stmt>(shared_from_this()); }

InterfaceDeclStmt::InterfaceDeclStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                                     const vector<std::shared_ptr<Stmt>> &decls,
                                     const SourcePos &sourcePos)
        : Stmt(InterfaceDeclStmtType, sourcePos), name(name),
          interfaceType(interfaceType), decls(decls) {
}

void InterfaceDeclStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "interface ";
    interfaceType->prettyPrint(out, depth + 1);
    out << ":" << endl;
    for (size_t i = 0; i < decls.size(); i++) {
        decls[i]->prettyPrint(out, depth + 1);
    }
    indent(out, 4 * depth);
    out << "endinterface" << endl;
}

shared_ptr<InterfaceDeclStmt>
InterfaceDeclStmt::interfaceDeclStmt() { return static_pointer_cast<InterfaceDeclStmt, Stmt>(shared_from_this()); }

InterfaceDefStmt::InterfaceDefStmt(const std::string &name, const std::shared_ptr<BSVType> &interfaceType,
                                     const vector<std::shared_ptr<Stmt>> &defs, const SourcePos &sourcePos)
        : Stmt(InterfaceDefStmtType, sourcePos), name(name),
          interfaceType(interfaceType), defs(defs) {
}

void InterfaceDefStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "interface ";
    interfaceType->prettyPrint(out, depth + 1);
    out << ":" << endl;
    for (size_t i = 0; i < defs.size(); i++) {
        defs[i]->prettyPrint(out, depth + 1);
    }
    indent(out, 4 * depth);
    out << "endinterface" << endl;
}

shared_ptr<InterfaceDefStmt>
InterfaceDefStmt::interfaceDefStmt() { return static_pointer_cast<InterfaceDefStmt, Stmt>(shared_from_this()); }


TypedefSynonymStmt::TypedefSynonymStmt(const std::shared_ptr<BSVType> &typedeftype,
                                       const std::shared_ptr<BSVType> &type,
                                       const SourcePos &sourcePos)
        : Stmt(TypedefSynonymStmtType, sourcePos), typedeftype(typedeftype), type(type) {

}

void TypedefSynonymStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "typedef ";
    type->prettyPrint(out, 0);
    out << " ";
    typedeftype->prettyPrint(out, 0);
    out << ":" << endl;
}

shared_ptr<TypedefSynonymStmt>
TypedefSynonymStmt::typedefSynonymStmt() { return static_pointer_cast<TypedefSynonymStmt, Stmt>(shared_from_this()); }

TypedefStructStmt::TypedefStructStmt(const std::string &name, const std::shared_ptr<BSVType> &structType,
                                     const std::vector<std::string> &members,
                                     const std::vector<std::shared_ptr<BSVType>> &memberTypes,
                                     const SourcePos &sourcePos)
        : Stmt(TypedefStructStmtType, sourcePos),
          name(name), structType(structType),
          members(members), memberTypes(memberTypes) {
}

void TypedefStructStmt::prettyPrint(ostream &out, int depth) {
    indent(out, 4 * depth);
    out << "typedef struct {" << endl;
    for (size_t i = 0; i < members.size(); i++) {
        indent(out, 4 * (depth + 1));
        memberTypes[i]->prettyPrint(out, depth + 1);
        out << " " << members[i] << ";" << endl;
    }
    indent(out, 4 * depth);
    out << "} ";
    structType->prettyPrint(out, depth);
    out << ":" << endl;
}

shared_ptr<TypedefStructStmt>
TypedefStructStmt::typedefStructStmt() { return static_pointer_cast<TypedefStructStmt, Stmt>(shared_from_this()); }

PackageDefStmt::PackageDefStmt(const string& name, const vector<shared_ptr<Stmt>> &stmts, const SourcePos &sourcePos)
    : Stmt(PackageDefStmtType, sourcePos), name(name),
    stmts(stmts), bindings() {
    for (int i = 0; i < stmts.size(); i++) {
        if (shared_ptr<ModuleDefStmt> moduleStmt = stmts[i]->moduleDefStmt()) {
            bindings[moduleStmt->name] = moduleStmt;
        }
    }
}

shared_ptr<Stmt> PackageDefStmt::lookup(const string &name)
{
    return bindings[name];
}

void PackageDefStmt::prettyPrint(ostream &out, int depth) {
    for (size_t i = 0; i < stmts.size(); i++) {
        indent(out, 4 * (depth + 1));
        stmts[i]->prettyPrint(out, depth + 1);
        out << " " << stmts[i] << ";" << endl;
    }
}
