//
// Created by Jamey Hicks on 10/28/19.
//

#include <sstream>
#include "GenerateKami.h"
#include "TopologicalSort.h"

GenerateKami::GenerateKami() {
    coqTypeMapping["TAdd"] = "add";
    coqTypeMapping["TSub"] = "sub";
    coqTypeMapping["TMul"] = "mul";
    coqTypeMapping["TDiv"] = "div";
    coqTypeMapping["TLog"] = "log2";

    kamiTypeMapping["TAdd"] = "add";
    kamiTypeMapping["TSub"] = "sub";
    kamiTypeMapping["TMul"] = "mul";
    kamiTypeMapping["TDiv"] = "div";
    kamiTypeMapping["TLog"] = "log2";
    kamiTypeMapping["Action"] = "Void";

}

void GenerateKami::open(const string &filename) {
    this->filename = filename;
    logstream << "Opening Kami file " << filename << endl;
    out.open(filename);
    logstream.open(filename + string(".kami.log"), ostream::out);

    string prelude[] = {
            "Require Import Bool String List.",
            "Require Import Lib.CommonTactics Lib.ilist Lib.Word.",
            "Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.",
            "Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.",
            "Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.",
            "Require Import Kami.Decomposition Kami.Notations Kami.Tactics.",
            "Require Import Kami.PrimFifo.",
            "Require Import Init.Nat.",
            "",
            "Require Import Ex.MemTypes.",
            "",
            "Set Implicit Arguments.",
            "Definition Bit := word.",
            "Definition Int := word.",
            "Open Scope string.",
            ""
    };
    for (size_t i = 0; i < sizeof(prelude) / sizeof(string); i++) {
        out << prelude[i] << endl;
    }
}

void GenerateKami::close() {
    logstream << "Closing Kami file " << filename << endl;
    out.close();
    logstream.close();
}

void GenerateKami::generateStmts(std::vector<shared_ptr<struct Stmt>> stmts, int depth) {
    std::vector<shared_ptr<struct Stmt>> sortedStmts = stmts; //sortStmts(stmts);
    for (int i = 0; i < sortedStmts.size(); i++) {
        shared_ptr<Stmt> stmt = sortedStmts[i];
        generateKami(stmt, depth);
        out << endl;
    }
}

void GenerateKami::generateModuleStmt(const shared_ptr<struct Stmt> &stmt, int depth, vector<shared_ptr<Stmt>> &actionStmts) {
    switch (stmt->stmtType) {
        case MethodDefStmtType:
            generateModuleStmt(stmt->methodDefStmt(), depth, actionStmts);
            break;
        case RegisterStmtType:
            generateModuleStmt(stmt->registerStmt(), depth, actionStmts);
            break;
        case RuleDefStmtType:
            generateModuleStmt(stmt->ruleDefStmt(), depth, actionStmts);
            break;
        default:
            out << "(* unhandled module stmt type " << stmt->stmtType << " at " << stmt->sourcePos.toString() << endl;
            out << "  ";
            stmt->prettyPrint(out);
            out << "*)" << endl;
    }
}


//void GenerateKami::generateModuleStmt(const shared_ptr<CallStmt> &callStmt, int depth) {
//    string functionName = callStmtFunctionName(callStmt);
//    indent(out, depth);
//    out << "(MEMod ((module'" << functionName << "." << functionName << " " << callStmt->name << ") :: nil) )" << endl;
//}

void GenerateKami::generateModuleStmt(const shared_ptr<MethodDefStmt> &methoddef, int depth, vector<shared_ptr<Stmt>> &actionStmts) {
    returnPending = "Retv";
    indent(out, depth);
    out << "Method (instancePrefix--\"" << methoddef->name << "\")";
    if (methoddef->params.size() == 0) {
        out << " ()";
    } else {
        for (int i = 0; i < methoddef->params.size(); i++) {
            out << " (";
            out << methoddef->params[i];
            out << " : ";
            generateKami(methoddef->paramTypes[i], depth + 1);
            out << ")";
        }
    }
    out << " : ";
    generateKami(methoddef->returnType, depth + 1);
    out << " := " << endl;
    indent(out, depth); out << "(" << endl;
    for (int i = 0; i < actionStmts.size(); i++) {
        generateKami(actionStmts[i], depth + 1);
        out << endl;
    }
    int num_stmts = methoddef->stmts.size();
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = methoddef->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";";
        }
        out << endl;
    }

    if (returnPending.size()) {
        indent(out, depth + 1);
        out << returnPending << endl;
    }
    indent(out, depth); out << ")" << endl;
}

void GenerateKami::generateModuleStmt(const shared_ptr<RegisterStmt> &registerStmt, int depth, vector<shared_ptr<Stmt>> &actionStmts) {
    indent(out, depth);
    out << "Register \"" << registerStmt->regName << "\" : ";
    //FIXME: placeholder for type
    generateKami(registerStmt->elementType, depth);
    out << " <- ";
    out << "Default";
}

void GenerateKami::generateModuleStmt(const shared_ptr<class RuleDefStmt> & ruledef, int depth, vector<shared_ptr<Stmt>> &actionStmts) {
    bool enclosingActionContext = actionContext;
    actionContext = true;
    returnPending = "Retv";

    indent(out, depth);
    out << "Rule (instancePrefix--\"" << ruledef->name << "\") := " << endl;
    indent(out, depth); out << "(" << endl;
    for (int i = 0; i < actionStmts.size(); i++) {
        generateKami(actionStmts[i], depth + 1);
        out << endl;
    }
    int num_stmts = ruledef->stmts.size();
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = ruledef->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";";
        }
        out << endl;
    }
    if (returnPending.size()) {
        indent(out, depth);
        out << returnPending << endl;
    }
    indent(out, depth); out << ")" << endl;

    actionContext = enclosingActionContext;
}

void GenerateKami::generateModuleStmt(const shared_ptr<VarBindingStmt> &stmt, int depth) {
    indent(out, depth);
    if (actionContext) {
        out << "LET " << stmt->name;
        if (stmt->bsvtype) {
            out << " : ";
            generateKami(stmt->bsvtype, depth);
        }
        if (stmt->rhs) {
            out << " <- ";
            generateKami(stmt->rhs, depth + 1);
        }
        out << " ;";
    }
}

void GenerateKami::generateKami(const shared_ptr<Stmt> &stmt, int depth) {
    switch (stmt->stmtType) {
        case ActionBindingStmtType:
            generateKami(stmt->actionBindingStmt(), depth);
            break;
        case VarBindingStmtType:
            generateKami(stmt->varBindingStmt(), depth);
            break;
        case BlockStmtType:
            generateKami(stmt->blockStmt(), depth);
            break;
        case CallStmtType:
            generateKami(stmt->callStmt(), depth);
            break;
        case ExprStmtType:
            generateKami(stmt->exprStmt(), depth);
            break;
        case FunctionDefStmtType:
            generateKami(stmt->functionDefStmt(), depth);
            break;
        case IfStmtType:
            generateKami(stmt->ifStmt(), depth);
            break;
        case ImportStmtType:
            generateKami(stmt->importStmt(), depth);
            break;
        case InterfaceDeclStmtType:
            generateKami(stmt->interfaceDeclStmt(), depth);
            break;
        case InterfaceDefStmtType:
            out << "(* interfaceDefStmt: " << endl;
            stmt->interfaceDefStmt()->prettyPrint(out, 1);
            out << "*)" << endl;
            break;
        case MethodDeclStmtType:
            generateKami(stmt->methodDeclStmt(), depth);
            break;
        case MethodDefStmtType:
            generateKami(stmt->methodDefStmt(), depth);
            break;
        case ModuleDefStmtType:
            generateKami(stmt->moduleDefStmt(), depth);
            break;
        case PatternMatchStmtType:
            out << "(* PatternMatchStmt" << endl;
            stmt->patternMatchStmt()->prettyPrint(out, 1);
            out << "*)" << endl;
            break;
        case RegReadStmtType:
            generateKami(stmt->regReadStmt(), depth);
            break;
        case RegWriteStmtType:
            generateKami(stmt->regWriteStmt(), depth);
            break;
        case ReturnStmtType:
            generateKami(stmt->returnStmt(), depth);
            break;
        case TypedefEnumStmtType:
            generateKami(stmt->typedefEnumStmt(), depth);
            break;
        case TypedefStructStmtType:
            generateKami(stmt->typedefStructStmt(), depth);
            break;
        case TypedefSynonymStmtType:
            generateKami(stmt->typedefSynonymStmt(), depth);
            break;
        case VarAssignStmtType:
            generateKami(stmt->varAssignStmt(), depth);
            break;
        case PackageDefStmtType:
            out << "(* Package: " << stmt->packageDefStmt()->name << " *)";
            break;
        case ModuleInstStmtType:
        case RegisterStmtType:
        case RuleDefStmtType:
        case InvalidStmtType:
            assert(0);
    }
}

void GenerateKami::generateKami(const shared_ptr<Expr> &expr, int depth, int precedence) {
    switch (expr->exprType) {
        case InvalidExprType:
            return;
        case ArraySubExprType: {
            shared_ptr<ArraySubExpr> arraySubExpr = expr->arraySubExpr();
            generateKami(arraySubExpr->array, depth+1, 0);
            out << " @[ ";
            generateKami(arraySubExpr->index, depth + 1, 0);
            out << " ]";
        } return;
        case BitSelExprType: {
            shared_ptr<BitSelExpr> bitSelExpr = expr->bitSelExpr();
            assert(bitSelExpr->lsb);
            generateKami(bitSelExpr->value, depth+1, 0);
            out << " @[ ";
            generateKami(bitSelExpr->msb, depth + 1, 0);
            out << " : ";
            generateKami(bitSelExpr->lsb, depth + 1, 0);
            out << " ]";
            out << " $width"; // fixme
        } return;
        case BitConcatExprType: {
            shared_ptr<BitConcatExpr> bitConcatExpr = expr->bitConcatExpr();
            out << "{ ";
            for (int i = 0; i < bitConcatExpr->values.size(); i++) {
                if (i > 0)
                    out << ", ";
                generateKami(bitConcatExpr->values[i], depth + 1);
            }
            out << " }";
        } return;
        case CallExprType:
            generateKami(expr->callExpr(), depth, precedence);
            return;
        case CondExprType: {
            shared_ptr<CondExpr> condExpr = expr->condExpr();
            out << endl;
            indent(out, depth);
            out << "(IF ";
            generateKami(condExpr->cond, depth + 1);
            out << " then ";
            generateKami(condExpr->thenExpr, depth + 1);
            out << " else ";
            generateKami(condExpr->elseExpr, depth + 1);
            out << ")";
        } return;
        case EnumUnionStructExprType: {
            shared_ptr<EnumUnionStructExpr> tagExpr = expr->enumUnionStructExpr();
            out << "(* tagged ";
            if (tagExpr->bsvtype)
                out << tagExpr->bsvtype->to_string();
            out << " *)" << tagExpr->tag;
        } return;
        case FieldExprType:
            generateKami(expr->fieldExpr(), depth, precedence);
            return;
        case MethodExprType:
            generateKami(expr->methodExpr(), depth, precedence);
            return;
        case SubinterfaceExprType:
            generateKami(expr->subinterfaceExpr(), depth, precedence);
            return;
        case IntConstType:
            out << "$" << expr->intConst()->value;
            return;
        case OperatorExprType:
            generateKami(expr->operatorExpr(), depth, precedence);
            return;
        case VarExprType:
            generateKami(expr->varExpr(), depth, precedence);
            return;
        case CaseExprType:
        case MatchesExprType:
            out << "Unflattened " << expr->exprType << " { ";
            expr->prettyPrint(out, depth);
            out << " }";
            break;
        case StringConstType:
            out << "\"" << expr->stringConst()->repr << "\"";
            break;
        case InterfaceExprType:
            out << "Unimplemented " << expr->exprType << " { ";
            expr->prettyPrint(out, depth);
            out << " }";
            break;
        case ValueofExprType:
            out << "Unimplemented " << expr->exprType << " { ";
            expr->prettyPrint(out, depth);
            out << " }";
            break;
    }
}

void GenerateKami::generateCoqType(const shared_ptr<BSVType> &bsvtype, int depth) {
    generateCoqType(out, bsvtype, depth);
}

void GenerateKami::generateCoqType(ostream &ostr, const shared_ptr<BSVType> &bsvtype, int depth) {
    if (bsvtype->params.size())
        ostr << "(";
    auto it = coqTypeMapping.find(bsvtype->name);
    if (it != coqTypeMapping.cend())
        ostr << it->second;
    else
        ostr << bsvtype->name;
    if (bsvtype->params.size()) {
        for (int i = 0; i < bsvtype->params.size(); i++) {
            ostr << " ";
            generateCoqType(ostr, bsvtype->params[i], depth);
        }
    }
    if (bsvtype->params.size())
        ostr << ")";
}

void GenerateKami::generateKami(const shared_ptr<BSVType> &bsvtype, int depth) {
    string name = bsvtype->name;
    auto it = kamiTypeMapping.find(name);
    if (it != kamiTypeMapping.cend())
        name = it->second;
    if (bsvtype->params.size())
        out << "(";
    if (bsvtype->name == "ActionValue" || bsvtype->name == "Numeric")
        generateKami(bsvtype->params[0], depth);
    else
        out << name;
    if (bsvtype->params.size()) {
        for (int i = 0; i < bsvtype->params.size(); i++) {
            out << " ";
            generateKami(bsvtype->params[i], depth);
        }
    }
    if (bsvtype->params.size())
        out << ")";
}

void GenerateKami::generateKami(const shared_ptr<ActionBindingStmt> &actionbinding, int depth) {
    shared_ptr<BSVType> bsvtype = actionbinding->bsvtype;
    if (bsvtype && bsvtype->name == "Reg") {
        indent(out, depth);
        out << "Register \"" << actionbinding->name << "\" : ";
        generateKami(bsvtype, depth+1);
        out << " <- Default";
        //FIXME: check for initializer
        //generateKami(actionbinding->rhs, depth + 1);
    } else {
        indent(out, depth);
        out << "Call ";
        //FIXME: Call
        generateKami(actionbinding->rhs, depth+1);
    }
}

void GenerateKami::generateKami(const shared_ptr<BlockStmt> &blockstmt, int depth) {
    int num_stmts = blockstmt->stmts.size();
    indent(out, depth);
    out << "(* block " << blockstmt->sourcePos.toString() << " *)" << endl;
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = blockstmt->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";" << endl;
        }
    }
    indent(out, depth);
    out << "(* endblock *)" << endl;

}

void GenerateKami::generateKami(const shared_ptr<CallStmt> &callStmt, int depth) {
    indent(out, depth);
    out << "Call " << callStmt->name << " : ";
    generateKami(callStmt->interfaceType, depth + 1);
    out << " <- ";
    generateKami(callStmt->rhs, depth + 1);
    out << " ;" << endl;
}

void GenerateKami::generateKami(const shared_ptr<ExprStmt> &stmt, int depth) {
    indent(out, depth);
    out << "(* expr " << stmt->expr->exprType << " *) ";
    generateKami(stmt->expr, depth + 1);
}


void GenerateKami::generateKami(const shared_ptr<FunctionDefStmt> &functiondef, int depth) {
    returnPending = "Retv";
    indent(out, depth);
    shared_ptr<BSVType> returnType = make_shared<BSVType>("Unknown");
    if (functiondef->returnType)
        returnType = functiondef->returnType;
    out << "Definition " << functiondef->name << " {ty} : (* args *) ActionT ty ";
    generateKami(returnType, depth);
    out << " := " << endl;
    indent(out, depth); out << "(" << endl;
    int num_stmts = functiondef->stmts.size();
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = functiondef->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";";
        }
        out << endl;
    }
    if (returnPending.size()) {
        indent(out, depth);
        out << returnPending << endl;
    }
    indent(out, depth); out << ")%kami_action." << endl;
}

void GenerateKami::generateKami(const shared_ptr<IfStmt> &stmt, int depth) {
    map<string,shared_ptr<BSVType>> assignedVars = stmt->attrs().assignedVars;
    returnPending = "Retv";

    indent(out, depth);
    out << "If (";
    generateKami(stmt->condition, depth + 1);
    out << ") then (" << endl;

    generateKami(stmt->thenStmt, depth + 1);
    out << endl;
    if (assignedVars.size()) {
        indent(out, depth + 1);
        out << "LET retval <- STRUCT { ";
        int i = 0;
        for (auto it = assignedVars.cbegin(); it != assignedVars.cend(); ++it, i++) {
            if (i > 0)
                out << ", ";
            out << " \"tpl_" << to_string(i) << "\" ::= #" << it->first;
        }
        out << " } ;" << endl;
        indent(out, depth + 1);
        returnPending = "Ret #retval";
    }
    if (returnPending.size()) {
        indent(out, depth + 1);
        out << returnPending << endl;
    }

    indent(out, depth);
    out << ") else (" << endl;
    if (stmt->elseStmt) {
        returnPending = "Retv";

        generateKami(stmt->elseStmt, depth + 1);

        if (assignedVars.size()) {
            indent(out, depth + 1);
            out << "LET retval <- STRUCT { ";
            int i = 0;
            for (auto it = assignedVars.cbegin(); it != assignedVars.cend(); ++it, i++) {
                if (i > 0)
                    out << ", ";
                out << " \"tpl_" << to_string(i) << "\" ::= #" << it->first;
            }
            out << " } ;" << endl;
            indent(out, depth + 1);
            returnPending = "Ret #retval";
        }

        if (returnPending.size()) {
            indent(out, depth + 1);
            out << returnPending << endl;
        }
    } else
        out << "Retv";
    out << endl;
    indent(out, depth);
    out << ") as retval ;" << endl;
    string structfields = formatStructDecl(assignedVars);
    int i = 0;
    for (auto it = assignedVars.cbegin(); it != assignedVars.cend(); ++it, i++) {
        indent(out, depth);
        out << "LET " << it->first << ": ";
        generateCoqType(it->second, depth);
        out << " <- (* assigned var *) #retval ! " << structfields << " @. \"tpl_" << to_string(i) << "\" ;" << endl;
    }
    returnPending = "Ret #retval";
}

void GenerateKami::generateKami(const shared_ptr<ImportStmt> &stmt, int depth) {
    out << "(* Require Import " << stmt->name << ". *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<InterfaceDeclStmt> &stmt, int depth) {
    out << "(* interface decl " << stmt->name << " *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<MethodDeclStmt> &stmt, int depth) {
    out << "(* method decl " << stmt->name << " *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<MethodDefStmt> &method, int depth) {
    returnPending = "Retv";
    out << "(* method def " << method->name << " *)" << endl;
    indent(out, depth);
    out << "Method \"" << method->name << "\" ";
    for (int i = 0; i < method->params.size(); i++) {
        indent(out, depth + 1);
        out << "( " << method->params[i] << " : ";
        generateCoqType(method->paramTypes[i], depth);
        out << ") ";
    }
    out << " := " << endl;
    for (int i = 0; i < method->stmts.size(); i++) {
        generateKami(method->stmts[i], depth + 1);
    }
    if (returnPending.size()) {
        indent(out, depth + 1);
        out << returnPending << endl;
    }
}

void GenerateKami::generateKami(const shared_ptr<ModuleDefStmt> &moduledef, int depth) {
    bool enclosingActionContext = actionContext;
    actionContext = true;
    instanceNames.clear();

    indent(out, depth);
    out << "Module module'" << moduledef->name << "." << endl;
    indent(out, depth);
    out << "  Section section'" << moduledef->name << "." << endl;

    indent(out, depth + 1);
    out << "Variable instancePrefix : string." << endl;

    for (int i = 0; i < moduledef->params.size(); i++) {
        indent(out, depth + 1);
        out << "Variable " << moduledef->params[i] << " : ";
        generateCoqType(moduledef->paramTypes[i], depth);
        out << "." << endl;
    }

    for (int i = 0; i < moduledef->stmts.size(); i++) {
        const shared_ptr<Stmt> &stmt = moduledef->stmts[i];
        if (stmt->stmtType == CallStmtType) {
            shared_ptr<CallStmt> callStmt = stmt->callStmt();
            instanceNames[callStmt->name] = callStmt->name;
            indent(out, depth + 1);
            out << "Definition " << callStmt->name << " : string := instancePrefix -- \"" << callStmt->name << "\"." << endl;
        }
    }

    indent(out, depth + 1);
    out << "Definition " << moduledef->name << " := " << "(MODULE {" << endl;

    vector<shared_ptr<Stmt>> actionStmts;
    for (int i = 0; i < moduledef->stmts.size(); i++) {

        shared_ptr<Stmt> stmt = moduledef->stmts[i];
        switch (stmt->stmtType) {
            case RegisterStmtType:
            case MethodDefStmtType:
            case RuleDefStmtType: {
                if (i != 0) {
                    indent(out, depth + 1);
                    out << "with " << endl;
                }
                generateModuleStmt(stmt, depth + 1, actionStmts);
                out << endl;
                break;
            }
            default: {
                actionStmts.push_back(stmt);
            }
        }

    }
    indent(out, depth + 1);
    out << "})." << endl;

    indent(out, depth);
    out << "  End section'" << moduledef->name << "." << endl;
    out << "End module'" << moduledef->name << "." << endl;

    actionContext = enclosingActionContext;
}

void GenerateKami::generateKami(const shared_ptr<RegReadStmt> &regread, int depth) {
    indent(out, depth);
    out << "Read "<< regread->var << " : ";
    generateKami(regread->varType, depth + 1);
    out << " <- \"" << regread->regName << "\"";
    out << " ;";
}

void GenerateKami::generateKami(const shared_ptr<RegWriteStmt> &regwrite, int depth) {
    indent(out, depth);
    out << "Write \"" << regwrite->regName << "\" : ";
    //FIXME: placeholder for type
    out << "Bit 32";
    out << " <- ";
    generateKami(regwrite->rhs, depth+1);
    out << " ;";
}

void GenerateKami::generateKami(const shared_ptr<ReturnStmt> &stmt, int depth) {
    returnPending = string();

    indent(out, depth);
    out << "Ret ";
    if (!stmt->value)
        logstream << "Bad return at " << stmt->sourcePos.toString() << endl;
    generateKami(stmt->value, depth+1);
}


void GenerateKami::generateKami(const shared_ptr<TypedefEnumStmt> &stmt, int depth) {
    logstream << "typedef enum " << stmt->enumType->to_string() << endl;
    out << "Definition " << stmt->name << "'Fields" << " := (STRUCT {\"$TAG\" :: Bit 4 })%kami." << endl;
    out << "Definition " << stmt->name << " := Struct " << stmt->name << "'Fields" << "." << endl;

    for (int i = 0; i < stmt->members.size(); i++) {
        out << "Notation \"'" << stmt->members[i] << "'\" := (STRUCT { \"$TAG\" ::= " << i << "})%init ." << endl;
    }
}

void GenerateKami::generateKami(const shared_ptr<TypedefStructStmt> &stmt, int depth) {
    logstream << "typedef struct " << stmt->structType->to_string() << endl;

    indent(out, depth);
    out << "(* Struct " << stmt->name << " at " << stmt->sourcePos.toString() << " *)" << endl;
    indent(out, depth);
    out << "Definition " << stmt->structType->name << "'Fields := (STRUCT {";
    for (int i = 0; i < stmt->members.size(); i++) {
        if (i > 0)
            out << ";";
        out << " \"" << stmt->members[i] << "\" :: ";
        generateKami(stmt->memberTypes[i], depth + 1);
    }
    out << "})%kami";
    out << "." << endl;
    out << "Definition " << stmt->structType->name << " := Struct " << stmt->structType->name << "'Fields ." << endl;
    out << endl;
}

void GenerateKami::generateKami(const shared_ptr<TypedefSynonymStmt> &stmt, int depth) {
    indent(out, depth);
    out << "Definition ";
    generateKami(stmt->typedeftype, depth + 1);
    out << " := ";
    generateKami(stmt->type, depth + 1);
    out << " .";
    out << endl;

}

void GenerateKami::generateKami(const shared_ptr<VarAssignStmt> &stmt, int depth) {
    shared_ptr<LValue> lvalue = stmt->lhs;
    switch (lvalue->lvalueType) {
        case ArraySubLValueType: {
            shared_ptr<ArraySubLValue> arraysubLvalue = lvalue->arraySubLValue();
            shared_ptr<Expr> array = arraysubLvalue->array;
            indent(out, depth);
            out << "LET ";
            generateKamiLHS(array);
            out << " <- ";
            generateKami(array, depth);
            out << " @[ ";
            generateKami(arraysubLvalue->index, depth + 1);
            out << " <- ";
            generateKami(stmt->rhs, depth + 1);
            out << " ]";
            out << " ; " << endl;
            break;
        }
        case FieldLValueType: {
            shared_ptr<FieldLValue> fieldLValue = lvalue->fieldLValue();
            shared_ptr<Expr> obj = fieldLValue->obj;
            indent(out, depth);
            out << "LET ";
            generateKamiLHS(obj);
            out << " <- ";
            generateKami(obj, depth);
            out << " ! ";
            generateCoqType(obj->bsvtype, depth + 1);
            out << " @{ \"" << fieldLValue->field << "\" <- ";
            generateKami(stmt->rhs, depth + 1);
            out << " } ; " << endl;
            break;
        }
        default: {
            shared_ptr<VarAssignStmt> varAssign = stmt->varAssignStmt();
            indent(out, depth);
            out << "(* VarAssignStmt *)" << endl;
            indent(out, depth);
            out << "LET ";
            generateKamiLHS(varAssign->lhs);
            out << " <- ";
            generateKami(varAssign->rhs, depth + 1);
            out << " ;";
            out << endl;
        }
    }
}
void GenerateKami::generateKami(const shared_ptr<VarBindingStmt> &stmt, int depth) {
    indent(out, depth);
    out << "(* varbinding " << depth << "*) ";
    if (actionContext) {
        out << "LET " << stmt->name;
        if (stmt->bsvtype) {
            out << " : ";
            generateKami(stmt->bsvtype, depth);
        }
        if (stmt->rhs) {
            out << " <- ";
            generateKami(stmt->rhs, depth + 1);
        }
        out << " ;";
    }
}

void GenerateKami::generateKami(const shared_ptr<FieldExpr> &expr, int depth, int precedence) {
    if (!expr->bsvtype) {
        expr->prettyPrint(logstream);
        logstream << endl;
    }
    generateKami(expr->object, depth, precedence);
    out << " ! (";
    assert(expr->bsvtype);
    generateKami(expr->object->bsvtype, depth);
    out << ") @. \"" << expr->fieldName << "\"";
}

void GenerateKami::generateKami(const shared_ptr<MethodExpr> &expr, int depth, int precedence) {
    logstream << "method expr ";
    expr->object->bsvtype->to_string();
    logstream << " " << expr->methodName << " at " << expr->sourcePos.toString() << endl;

    generateKami(expr->object, depth, precedence);
    out << " -- (* method *) \"" << expr->methodName << "\"";
}

void GenerateKami::generateKami(const shared_ptr<SubinterfaceExpr> &expr, int depth, int precedence) {
    logstream << "subinterface expr ";
    expr->object->bsvtype->to_string();
    logstream << " " << expr->subinterfaceName << " at " << expr->sourcePos.toString() << endl;

    generateKami(expr->object, depth, precedence);
    out << " -- (* subinfc *) \"" << expr->subinterfaceName << "\"";
}

void GenerateKami::generateKami(const shared_ptr<VarExpr> &expr, int depth, int precedence) {
    out << "#" << expr->name;
}

void GenerateKami::generateKami(const shared_ptr<CallExpr> &expr, int depth, int precedence) {
    shared_ptr<Expr> functionExpr = expr->function;
    out << "(MethodSig (";
    generateMethodName(functionExpr);
    out << ")";
    if (expr->args.size()) {
        for (int i = 0; i < expr->args.size(); i++) {

            out << " (";
            if (expr->args[i]->bsvtype) {
                generateKami(expr->args[i]->bsvtype, depth + 1);
            } else {
                out << "_";
            }
            out << ")";
        }
    } else {
        out << " ()";
    }
    out << " : Void) ";

    if (expr->args.size()) {
        for (int i = 0; i < expr->args.size(); i++) {

            out << " (";
            generateKami(expr->args[i], depth + 1);
            out << ")";
        }
    } else {
        out << " ()";
    }
}

void GenerateKami::generateMethodName(const shared_ptr<Expr> &expr) {
    switch (expr->exprType) {
        case FieldExprType: {
            shared_ptr<FieldExpr> fieldExpr = expr->fieldExpr();
            generateMethodName(fieldExpr->object);
            out << " -- \"" << fieldExpr->fieldName << "\"";
        } break;
        case MethodExprType: {
            shared_ptr<MethodExpr> methodExpr = expr->methodExpr();
            generateMethodName(methodExpr->object);
            out << " -- \"" << methodExpr->methodName << "\"";
        } break;
        case SubinterfaceExprType: {
            shared_ptr<SubinterfaceExpr> subinterfaceExpr = expr->subinterfaceExpr();
            generateMethodName(subinterfaceExpr->object);
            out << " -- \"" << subinterfaceExpr->subinterfaceName << "\"";
        } break;
        case VarExprType: {
            shared_ptr<VarExpr> varExpr = expr->varExpr();
            if (instanceNames[varExpr->name].size()) {
                out << varExpr->name;
            } else {
                out << "\"" << varExpr->name << "\"";
            }
        } break;
        default:
            out << "(* unhandled function name " << expr->exprType << " *) ";
            expr->prettyPrint(out);
    }
}

void GenerateKami::generateKami(const shared_ptr<IntConst> &expr, int depth, int precedence) {
    out << expr->value;
}

void GenerateKami::generateKami(const shared_ptr<OperatorExpr> &expr, int depth, int precedence) {
    if (!expr->rhs)
        out << expr->op << " ";
    generateKami(expr->lhs, depth, precedence);
    if (expr->rhs) {
        out << " " << expr->op << " ";
        generateKami(expr->rhs, depth, precedence);
    }
}

void GenerateKami::generateKami(const shared_ptr<ArraySubExpr> &expr, int depth, int precedence) {
    out << "( ";
    generateKami(expr->array, depth + 1, precedence);
    out << " ! (* array sub *) ";
    generateKami(expr->index, depth + 1, precedence);
    out << " )";
}

void GenerateKami::generateKami(const shared_ptr<BitSelExpr> &expr, int depth, int precedence) {
    out << "( ";
    generateKami(expr->value, depth + 1, precedence);
    out << " ! (* array sub *) ";
    generateKami(expr->msb, depth + 1, precedence);
    out << " , ";
    generateKami(expr->lsb, depth + 1, precedence);
    out << " )";
}

void GenerateKami::generateKami(const shared_ptr<EnumUnionStructExpr> &expr, int depth, int precedence) {
    out << "STRUCT { ";
    for (int i = 0; i < expr->keys.size(); i++) {
        if (i > 0)
            out << "; ";
        out << " \"" << expr->keys[i] << " : ";
        generateKami(expr->vals[i], depth + 1, precedence);
    }
    out << " }";
}

string GenerateKami::callStmtFunctionName(const shared_ptr<CallStmt> &callStmt)
{
    shared_ptr<Expr> rhs = callStmt->rhs;
    shared_ptr<CallExpr> callExpr = rhs->callExpr();
    shared_ptr<Expr> function = callExpr->function;
    shared_ptr<VarExpr> varExpr = function->varExpr();
    return varExpr->name;
}

std::vector<shared_ptr<struct Stmt>> GenerateKami::sortStmts(vector<shared_ptr<struct Stmt>> stmts) {
    Graph g(stmts.size());

    return std::vector<shared_ptr<struct Stmt>>();
}

void GenerateKami::generateKamiLHS(const shared_ptr<Expr> &expr) {
    switch (expr->exprType) {
        case VarExprType:
            out << expr->varExpr()->name;
            break;
        default:
            assert(expr->exprType == VarExprType);
            //FIXME what else do we see here?
    }

}

void GenerateKami::generateKamiLHS(const shared_ptr<LValue> &lvalue) {
    switch (lvalue->lvalueType) {
        case VarLValueType:
            out << lvalue->varLValue()->name;
            break;
        default:
            assert(lvalue->lvalueType == VarLValueType);
    }
}

string GenerateKami::formatStructDecl(const map<string,shared_ptr<BSVType>> &assignedVars) {
    ostringstream result;
    result << "STRUCT { ";
    int i = 0;
    for (auto it = assignedVars.cbegin(); it != assignedVars.cend(); ++it, ++i) {
        if (i > 0)
            result << ", ";
        result << "\"" << it->first << "\" :: ";
        generateCoqType(result, it->second, 0);
    }
    result << " } ";
    return result.str();
}

