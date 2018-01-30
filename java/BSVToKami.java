import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;

class CallVisitor extends BSVBaseVisitor<BSVParser.CallexprContext> {
    @Override public BSVParser.CallexprContext visitCallexpr(BSVParser.CallexprContext ctx) { return ctx; }
}

class RegReadVisitor extends BSVBaseVisitor<Void> {
    public TreeMap<String,BSVType> regs = new TreeMap<>();
    final SymbolTable scope;
    RegReadVisitor(SymbolTable scope) {
        this.scope = scope;
    }

    @Override public Void visitVarexpr(BSVParser.VarexprContext ctx) {
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
            if (scope.containsKey(varName)) {
                SymbolTableEntry entry = scope.lookup(varName);
                if (entry.type.name.startsWith("Reg")) {
                    regs.put(varName, entry.type.params.get(0));
                }
            }
        }
        return null;
    }
}

class BSVExpressionConverter extends BSVBaseVisitor<Expression>
{
        @Override
        public Expression visitIdentifier(BSVParser.IdentifierContext ctx) {
            return new VariableRead(ctx.getText());
        }
        @Override
        public Expression visitCondExpr(BSVParser.CondExprContext ctx) {
            return new CondExpression(visit(ctx.pred),
                                      visit(ctx.expression(0)),
                                      visit(ctx.expression(1)));
        }
        @Override
        public Expression visitSimpleCondExpr(BSVParser.SimpleCondExprContext ctx) {
            return new CondExpression(visit(ctx.binopexpr()),
                                      visit(ctx.expression(0)),
                                      visit(ctx.expression(1)));
        }
        @Override public Expression visitBinopexpr(BSVParser.BinopexprContext ctx) {
            if (ctx.left == null) {
                return visit(ctx.unopexpr());
            } else {
                Expression left = visit(ctx.left);
                String op = ctx.op.getText();
                if (ctx.right != null) {
                    return new OperatorExpression(op, left, visit(ctx.right));
                } else {
                    return new OperatorExpression(op, left);
                }
            }
        }
        @Override public Expression visitUnopexpr(BSVParser.UnopexprContext ctx) {
            if (ctx.op != null) {
                String op = ctx.op.getText();
                if (ctx.exprprimary() != null) {
                    return new OperatorExpression(op, visit(ctx.exprprimary()));
                } else {
                    return new OperatorExpression(op, visit(ctx.unopexpr()));
                }
            } else {
                return visit(ctx.exprprimary());
            }
        }
    @Override public Expression visitIntliteral(BSVParser.IntliteralContext ctx) {
        return new IntExpression(ctx.IntLiteral().getText());
    }
    @Override public Expression visitRealliteral(BSVParser.RealliteralContext ctx) {
        return new RealExpression(ctx.RealLiteral().getText());
    }
}

public class BSVToKami extends BSVBaseVisitor<Void>
{
    private final StaticAnalysis scopes;
    private SymbolTable scope;
    private String pkgName;
    private Package pkg;
    private ModuleDef moduleDef;
    private BSVExpressionConverter expressionConverter;
    BSVToKami(String pkgName, StaticAnalysis scopes) {
        this.scopes = scopes;
        this.pkgName = pkgName;
        expressionConverter = new BSVExpressionConverter();
        pkg = new Package(pkgName);
    }

    @Override
    public Void visitPackagedef(BSVParser.PackagedefContext ctx) {
        System.err.println("Package " + pkgName);

        System.out.println("Require Import Bool String List.");
        System.out.println("Require Import Lib.CommonTactics Lib.ilist Lib.Word.");
        System.out.println("Require Import Lib.Struct Lib.FMap Lib.StringEq Lib.Indexer.");
        System.out.println("");
        System.out.println("Require Import Kami.Syntax Kami.Notations Kami.Semantics Kami.Wf.");
        System.out.println("Require Import Kami.Inline Kami.InlineFacts.");
        System.out.println("Require Import Kami.RefinementFacts Kami.Decomposition.");
        System.out.println("Require Import Kami.Tactics.");
        System.out.println("");
        System.out.println("Require Import FunctionalExtensionality.");
        System.out.println("");
        System.out.println("Set Implicit Arguments.");
        System.out.println("");

        if (ctx.packagedecl() != null) {
            if (!pkgName.equals(ctx.packagedecl().pkgname)) {
                System.err.println("Expected " + pkgName + " found " + ctx.packagedecl().pkgname);
            }
        }
        return visitChildren(ctx);
    }

    @Override public Void visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) {
        scope = scopes.getScope(ctx);
        visitChildren(ctx);
        scope = scope.parent;
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        for (BSVParser.AttributeinstanceContext attrinstance: ctx.attributeinstance()) {
            for (BSVParser.AttrspecContext attr: attrinstance.attrspec()) {
                if (attr.identifier().getText().equals("nogen"))
                return null;
            }
        }
        scope = scopes.getScope(ctx);
        String moduleName = ctx.moduleproto().name.getText();
        String sectionName = moduleName.startsWith("mk") ? moduleName.substring(2) : moduleName;
        moduleDef = new ModuleDef(moduleName);
        pkg.addStatement(moduleDef);
        System.err.println("module " + moduleName);
        System.out.println("Section " + sectionName + ".");
        System.out.println("    Definition " + moduleName + " := MODULE {" + "\n");
        String prefix = "    ";
        for (BSVParser.ModulestmtContext modulestmt: ctx.modulestmt()) {
            System.out.print(prefix);
            visit(modulestmt);
            prefix = "    with ";
        }
        System.out.println("    }. (*" + ctx.moduleproto().name.getText() + " *)" + "\n");
        System.out.println("End " + sectionName + ".");
        scope = scope.parent;
        moduleDef = null;
        System.err.println("endmodule : " + moduleName);
        return null;
    }

    BSVParser.CallexprContext getCall(ParserRuleContext ctx) {
        return new CallVisitor().visit(ctx);
    }

    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            System.out.print("    Variable " + varName + ": " + entry.type);
            BSVParser.ExpressionContext rhs = varinit.rhs;
            if (rhs != null) {
                expressionConverter.visit(rhs);
                System.out.print(" = ");
                visit(rhs);
            }
            System.out.println(".");
        }
        return null;
    }
    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVParser.ExpressionContext rhs = ctx.rhs;
        Expression expr = expressionConverter.visit(rhs);
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            System.out.print("    Variable " + varName + ": " + entry.type + " ");
        }
        if (ctx.op != null) {
            System.out.print("    " + ctx.op.getText());
            visit(ctx.rhs);
        }
        System.out.println(".");
        return null ;
    }
    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
        String typeName = ctx.t.getText();
        String varName = ctx.var.getText();
        BSVParser.ExpressionContext rhs = ctx.rhs;
        Expression expr = expressionConverter.visit(rhs);
        SymbolTableEntry entry = scope.lookup(varName);
        BSVType bsvtype = entry.type;
        if (typeName.startsWith("Reg")) {
            BSVType paramtype = bsvtype.params.get(0);
            System.out.print("Register \"" + varName + "\" : " + bsvTypeToKami(paramtype)
                             + " <- ");

            BSVParser.CallexprContext call = getCall(ctx.rhs);
            if (call != null && call.fcn != null && call.fcn.getText().equals("mkReg")) {
                System.out.print("$" + call.expression().get(0).getText());
            } else {
                visit(ctx.rhs);
            }

            System.out.println("");
        } else {
            BSVType paramtype = bsvtype.params.get(0);
            System.out.print("    LET \"" + varName + "\" : " + bsvTypeToKami(paramtype)
                             + " <- ");

            BSVParser.CallexprContext call = getCall(ctx.rhs);
            if (call != null && call.fcn != null && call.fcn.getText().equals("mkReg")) {
                System.out.print(call.expression().get(0).getText());
            } else {
                visit(ctx.rhs);
            }

            System.out.println("");
        }
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
        scope = scopes.getScope(ruledef);
        String ruleName = ruledef.name.getText();
        RuleDef ruleDef = new RuleDef(ruleName);
        BSVParser.RulecondContext rulecond = ruledef.rulecond();
        moduleDef.addRule(ruleDef);

        System.out.println("Rule \"" + ruleName + "\" :=" + "\n");
        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        if (rulecond != null) regReadVisitor.visit(rulecond);
        for (BSVParser.StmtContext stmt: ruledef.stmt()) {
            regReadVisitor.visit(stmt);
        }
        for (Map.Entry<String,BSVType> entry: regReadVisitor.regs.entrySet()) {
            String regName = entry.getKey();
            System.out.println("        Read " + regName + "_v : " + bsvTypeToKami(entry.getValue()) + " <- \"" + regName + "\";");
        }

        if (rulecond != null) {
            System.out.print("        Assert(");
            visit(rulecond);
            System.out.println(");");
        }
        for (BSVParser.StmtContext stmt: ruledef.stmt()) {
            visit(stmt);
        }
        System.out.println("        Retv (* rule " + ruledef.name.getText() + " *)" + "\n");
        scope = scope.parent;
        return null;
    }

    @Override public Void visitRegwrite(BSVParser.RegwriteContext regwrite) {
        System.out.print("        Write \"");
        visit(regwrite.lhs);
        System.out.print("\" <- ");
        visit(regwrite.rhs);
        System.out.println(";" + "\n");
        return null;
    }
    @Override public Void visitVarassign(BSVParser.VarassignContext ctx) {
        System.out.print("        Assign ");
        boolean multi = ctx.lvalue().size() > 1;
        int count = 0;
        if (multi) System.out.print("{ ");
        for (BSVParser.LvalueContext lvalue: ctx.lvalue()) {
            if (multi && count > 0) System.out.print(", ");
            System.out.print(lvalue.getText());
            count++;
        }
        if (multi) System.out.print(" }");
        System.out.print(" " + ctx.op.getText() + " ");
        visit(ctx.expression());
        System.out.println(";" + "\n");
        return null;
    }

    @Override
    public Void visitIfstmt(BSVParser.IfstmtContext ctx) {
        System.out.print("        (If ");
        visit(ctx.condpredicate());
        System.out.println("");
        System.out.print("        then ");
        visit(ctx.stmt(0));
        System.out.print("        Retv;");
        if (ctx.stmt(1) != null) {
            System.out.println("");
            System.out.print("        else ");
            visit(ctx.stmt(1));
            System.out.print("        Retv;");
        }
        System.out.println(")");
        return null;
    }
    @Override public Void visitCasestmt(BSVParser.CasestmtContext ctx) {
        visitChildren(ctx);
        return null;
    }
    @Override
    public Void visitPattern(BSVParser.PatternContext ctx) {
        //FIXME
        System.out.print("$" + ctx.getText());
        return null;
    }

    @Override
    public Void visitCondpredicate(BSVParser.CondpredicateContext ctx) {
        visit(ctx.expression());
        // if (ctx.pattern() != null) {
        //     System.out.print(" matches ");
        //     visit(ctx.pattern());
        // }
        if (ctx.condpredicate() != null) {
            System.out.print(" && ");
            visit(ctx.condpredicate());
        }
        return null;
    }
    @Override public Void visitBinopexpr(BSVParser.BinopexprContext expr) {
        if (expr.right != null) {
            System.out.print("(");
            if (expr.left != null)
                visit(expr.left);
            if (expr.op != null) {
                System.out.print(" " + expr.op.getText() + " ");
            }

            visit(expr.right);
            System.out.print(")");
        } else {
            visitChildren(expr);
        }
        return null;
    }
    @Override public Void visitUnopexpr(BSVParser.UnopexprContext ctx) {
        if (ctx.op != null) {
            System.out.print(ctx.op.getText());
        }
        return visitChildren(ctx);
    }
    @Override public Void visitIntliteral(BSVParser.IntliteralContext ctx) {
        System.out.print("$" + ctx.IntLiteral().getText());
        return null;
    }
    @Override public Void visitRealliteral(BSVParser.RealliteralContext ctx) {
        System.out.print("$" + ctx.RealLiteral().getText());
        return null;
    }
    @Override public Void visitVarexpr(BSVParser.VarexprContext ctx) {
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
            System.err.println("var " + varName + " scope " + scope);
            if (scope.containsKey(varName)) {
                SymbolTableEntry entry = scope.lookup(varName);
                System.err.println("found binding " + varName + " " + entry.type);
                if (entry.type.name.startsWith("Reg"))
                    System.out.print("#" + varName + "_v");
                else
                    System.out.print(varName);
            } else {
                System.out.print(varName);
            }
        }
        return null;
    }
    @Override public Void visitArraysub(BSVParser.ArraysubContext ctx) {
        visit(ctx.array);
        System.out.print("[");
        visit(ctx.expression(0));
        if (ctx.expression(1) != null) {
            System.out.print(" : ");
            visit(ctx.expression(1));
        }
        System.out.print("]");
        return null;
    }
    @Override public Void visitLvalue(BSVParser.LvalueContext ctx) {
        if (ctx.lvalue() != null) {
            visit(ctx.lvalue());
        }
        if (ctx.index != null) {
            System.out.print("[");
            visit(ctx.index);
            System.out.print("]");
        } else if (ctx.msb != null) {
            System.out.print("[");
            visit(ctx.msb);
            System.out.print(", ");
            visit(ctx.lsb);
            System.out.print("]");
        } else if (ctx.lowerCaseIdentifier() != null) {
            if (ctx.lvalue() != null)
                System.out.print(".");
            System.out.print(ctx.lowerCaseIdentifier().getText());
        }
        return null;
    }

    public String bsvTypeToKami(BSVType t) {
        if (t == null)
            return "<nulltype>";
        t = t.prune();
        String kamitype = t.name;
        for (BSVType p: t.params)
            kamitype += " " + bsvTypeToKami(p);
        return kamitype;
    }
}
