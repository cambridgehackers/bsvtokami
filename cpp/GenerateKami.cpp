//
// Created by Jamey Hicks on 10/28/19.
//

#include "GenerateKami.h"


GenerateKami::GenerateKami() : containsReturn(false) {

}

void GenerateKami::open(const string &filename) {
    this->filename = filename;
    cerr << "Opening Kami file " << filename << endl;
    out.open(filename);

    string prelude[] = {
            "Require Import Bool String List.",
            "Require Import Lib.CommonTactics Lib.ilist Lib.Word.",
            "Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.",
            "Require Import Kami.Syntax Kami.Semantics Kami.RefinementFacts Kami.Renaming Kami.Wf.",
            "Require Import Kami.Renaming Kami.Inline Kami.InlineFacts.",
            "Require Import Kami.Decomposition Kami.Notations Kami.Tactics.",
            "Require Import Kami.PrimFifo.",
            "",
            "Require Import Ex.MemTypes.",
            "",
            "Set Implicit Arguments.",
            "Open Scope string.",
            ""
    };
    for (size_t i = 0; i < sizeof(prelude) / sizeof(string); i++) {
        out << prelude[i] << endl;
    }
}

void GenerateKami::close() {
    cerr << "Closing Kami file " << filename << endl;
    out.close();
}

void GenerateKami::generateStmts(std::vector<shared_ptr<struct Stmt>> stmts) {
    for (int i = 0; i < stmts.size(); i++) {
        shared_ptr<Stmt> stmt = stmts[i];
        generateKami(stmt);
        out << endl;
    }
}

void GenerateKami::generateKami(shared_ptr<Stmt> stmt, int depth) {
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
        case RegisterStmtType:
            generateKami(stmt->registerStmt(), depth);
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
        case RuleDefStmtType:
            generateKami(stmt->ruleDefStmt(), depth);
            break;
        case TypedefStructStmtType:
            generateKami(stmt->typedefStructStmt(), depth);
            break;
        case TypedefSynonymStmtType:
            generateKami(stmt->typedefSynonymStmt(), depth);
            break;
        case VarAssignStmtType:
            out << "(* VarAssignStmt" << endl;
            stmt->varAssignStmt()->prettyPrint(out, 1);
            out << "*)" << endl;
            break;
        case PackageDefStmtType:
            out << "(* Package: " << stmt->packageDefStmt()->name << " *)";
            break;
        case ModuleInstStmtType:
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
            out << "(* tagged *)" << tagExpr->tag;
        } return;
        case FieldExprType:
            generateKami(expr->fieldExpr(), depth, precedence);
            return;
        case IntConstType:
            out << expr->intConst()->value;
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
            out << "Unimplemented " << expr->exprType << " { ";
            expr->prettyPrint(out, depth);
            out << " }";
    }
}

void GenerateKami::generateKami(const shared_ptr<BSVType> &bsvtype, int depth) {
    if (bsvtype->params.size())
        out << "(";
    if (bsvtype->name == "Action")
        out << "Void";
    else if (bsvtype->name == "ActionValue")
        generateKami(bsvtype->params[0]);
    else
        out << bsvtype->name;
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
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = blockstmt->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";" << endl;
        }
    }
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
    indent(out, depth); out << ")%kami_action." << endl;
}

void GenerateKami::generateKami(const shared_ptr<IfStmt> &stmt, int depth) {
    indent(out, depth);
    out << "If (";
    generateKami(stmt->condition, depth + 1);
    out << ") then (" << endl;

    containsReturn = false;
    generateKami(stmt->thenStmt, depth + 1);
    if (!containsReturn)
        out << "Retv";
    out << endl;

    indent(out, depth);
    out << ") else (" << endl;
    if (stmt->elseStmt) {
        containsReturn = false;

        generateKami(stmt->elseStmt, depth + 1);
        if (!containsReturn)
            out << "Retv";
    } else
        out << "Retv";
    out << endl;
    indent(out, depth);
    out << ") as v; Ret v" << endl;
}

void GenerateKami::generateKami(const shared_ptr<ImportStmt> &stmt, int depth) {
    out << "(* import " << stmt->name << " *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<InterfaceDeclStmt> &stmt, int depth) {
    out << "(* interface decl " << stmt->name << " *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<MethodDeclStmt> &stmt, int depth) {
    out << "(* method decl " << stmt->name << " *)" << endl;
}

void GenerateKami::generateKami(const shared_ptr<MethodDefStmt> &methoddef, int depth) {
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
    int num_stmts = methoddef->stmts.size();
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = methoddef->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";";
        }
        out << endl;
    }
    
    if (!containsReturn) {
        indent(out, depth + 1);
        out << "Retv " << endl;
    }
    indent(out, depth); out << ")" << endl;
}

void GenerateKami::generateKami(const shared_ptr<ModuleDefStmt> &moduledef, int depth) {
    bool enclosingActionContext = actionContext;
    actionContext = true;

    indent(out, depth);
    out << "Module module'" << moduledef->name << "." << endl;
    indent(out, depth);
    out << "  Section section'" << moduledef->name << "." << endl;

    indent(out, depth + 1);
    out << "Variable instancePrefix : string." << endl;
    indent(out, depth + 1);
    out << "Definition " << moduledef->name << " := " << "(MODULE {" << endl;

    for (int i = 0; i < moduledef->stmts.size(); i++) {
        if (i != 0) {
            indent(out, depth + 1);
            out << "with " << endl;
        }
        shared_ptr<Stmt> stmt = moduledef->stmts[i];
        generateKami(stmt, depth + 1);
        out << endl;
    }
    indent(out, depth + 1);
    out << "})." << endl;

    indent(out, depth);
    out << "  End section'" << moduledef->name << "." << endl;
    out << "End module'" << moduledef->name << "." << endl;

    actionContext = enclosingActionContext;
}

void GenerateKami::generateKami(const shared_ptr<RegisterStmt> &registerStmt, int depth) {
    indent(out, depth);
    out << "Register \"" << registerStmt->regName << "\" : ";
    //FIXME: placeholder for type
    generateKami(registerStmt->elementType, depth);
    out << " <- ";
    out << "Default";
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
    containsReturn = true;

    indent(out, depth);
    out << "Ret ";
    generateKami(stmt->value, depth+1);
}

void GenerateKami::generateKami(const shared_ptr<RuleDefStmt> &ruledef, int depth) {
    bool enclosingActionContext = actionContext;
    actionContext = true;

    indent(out, depth);
    out << "Rule (instancePrefix--\"" << ruledef->name << "\") := " << endl;
    indent(out, depth); out << "(" << endl;
    int num_stmts = ruledef->stmts.size();
    for (int i = 0; i < num_stmts; i++) {
        shared_ptr<Stmt> stmt = ruledef->stmts[i];
        generateKami(stmt, depth + 1);
        if (i < num_stmts - 1) {
            //out << ";";
        }
        out << endl;
    }
    indent(out, depth + 1); out << "Retv " << endl;
    indent(out, depth); out << ")" << endl;

    actionContext = enclosingActionContext;
}

void GenerateKami::generateKami(const shared_ptr<TypedefStructStmt> &stmt, int depth) {
    indent(out, depth);
    out << "Definition ";
    generateKami(stmt->structType, depth + 1);
    out << " := STRUCT {";
    for (int i = 0; i < stmt->members.size(); i++) {
        if (i > 0)
            out << ";";
        out << " \"" << stmt->members[i] << " : ";
        generateKami(stmt->memberTypes[i], depth + 1);
    }
    out << "} ;";
    out << endl;
}

void GenerateKami::generateKami(const shared_ptr<TypedefSynonymStmt> &stmt, int depth) {
    indent(out, depth);
    out << "Definition ";
    generateKami(stmt->typedeftype, depth + 1);
    out << " := ";
    generateKami(stmt->type, depth + 1);
    out << " ;";
    out << endl;

}

void GenerateKami::generateKami(const shared_ptr<VarBindingStmt> &stmt, int depth) {
    indent(out, depth);
    if (actionContext) {
        out << "LET " << stmt->name;
        if (stmt->bsvtype) {
            out << " : ";
            generateKami(stmt->bsvtype);
        }
        if (stmt->rhs) {
            out << " <- ";
            generateKami(stmt->rhs, depth + 1);
        }
        out << " ;";
    }
}

void GenerateKami::generateKami(const shared_ptr<FieldExpr> &expr, int depth, int precedence) {
    generateKami(expr->object, depth, precedence);
    out << " ! ";
    out << "(* struct type *)"; //FIXME struct type
    out << " @. \"" << expr->fieldName << "\"";
}

void GenerateKami::generateKami(const shared_ptr<VarExpr> &expr, int depth, int precedence) {
    out << "#" << expr->name;
}

void GenerateKami::generateKami(const shared_ptr<CallExpr> &expr, int depth, int precedence) {
    shared_ptr<Expr> functionExpr = expr->function;
    if (functionExpr->exprType == FieldExprType) {
        shared_ptr<FieldExpr> fieldExpr = functionExpr->fieldExpr();
        shared_ptr<VarExpr> varExpr = fieldExpr->object->varExpr();
        out << "\"";
        fieldExpr->object->prettyPrint(out, 0);
        out << "." << fieldExpr->fieldName << "\"";
    } else {
        generateKami(functionExpr, depth, precedence);
    }
    out << "( ";
    for (int i = 0; i < expr->args.size(); i++) {
        if (i > 0)
            out << ", ";
        expr->args[i]->prettyPrint(out, depth + 1);
    }
    out << " )";
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


