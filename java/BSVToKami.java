import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;

class CallVisitor extends BSVBaseVisitor<BSVParser.CallexprContext> {
    @Override public BSVParser.CallexprContext visitCallexpr(BSVParser.CallexprContext ctx) { return ctx; }
}
class InstanceNameVisitor extends BSVBaseVisitor<String> {
    private final SymbolTable scope;
    InstanceNameVisitor(SymbolTable scope) {
	this.scope = scope;
    }
    @Override public String visitOperatorExpr(BSVParser.OperatorExprContext ctx) {
	String instanceName = visit(ctx.binopexpr());
	System.err.println("visitOperatorExpr " + ctx.getRuleIndex() + " " + ctx.getText() + " " + instanceName);
	return instanceName;
    }
    @Override public String visitBinopexpr(BSVParser.BinopexprContext ctx) {
	String instanceName = null;
	if (ctx.unopexpr() != null) {
	    instanceName = visit(ctx.unopexpr());
	}
	System.err.println("visitBinopexpr " + ctx.getRuleIndex() + " " + ctx.getText() + " " + instanceName);
	return instanceName;
    }
    @Override public String visitUnopexpr(BSVParser.UnopexprContext ctx) {
	String instanceName = null;
	if (ctx.op == null)
	    instanceName = visit(ctx.exprprimary());
	System.err.println("visitUnopexpr " + ctx.getRuleIndex() + " " + ctx.getText() + " " + instanceName);
	return instanceName;
    }
    @Override public String visitCallexpr(BSVParser.CallexprContext ctx) {
	return visit(ctx.fcn);
    }
    @Override public String visitFieldexpr(BSVParser.FieldexprContext ctx) {
	String instanceName = visit(ctx.exprprimary());
	if (instanceName != null) {
	    String fieldName = String.format("%s.%s", instanceName.substring(1), ctx.exprfield.getText());
	    System.err.println("Fieldname " + fieldName);
	    return fieldName;
	}
	return null;
    }
    @Override public String visitVarexpr(BSVParser.VarexprContext ctx) {
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
	    SymbolTableEntry entry = scope.lookup(varName);
	    if (entry != null) {
		if (entry.instanceName != null) {
		    System.err.println(String.format("Instancename %s -> %s", varName, entry.instanceName));
		    return entry.instanceName;
		}
            } else {
		System.err.println(String.format("No symbol table entry for %s", varName));
	    }
        }
        return null;
    }
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


public class BSVToKami extends BSVBaseVisitor<Void>
{
    private final StaticAnalysis scopes;
    private SymbolTable scope;
    private String pkgName;
    private Package pkg;
    private ModuleDef moduleDef;
    private ArrayList<String> instances;
    private boolean actionContext;
    BSVToKami(String pkgName, StaticAnalysis scopes) {
        this.scopes = scopes;
        this.pkgName = pkgName;
        pkg = new Package(pkgName);
	actionContext = false;
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
	instances = new ArrayList<>();
        scope = scopes.getScope(ctx);
        String moduleName = ctx.moduleproto().name.getText();
        String sectionName = moduleName.startsWith("mk") ? moduleName.substring(2) : moduleName;
        moduleDef = new ModuleDef(moduleName);
        pkg.addStatement(moduleDef);
        System.err.println("module " + moduleName);
        System.out.println("Section " + sectionName + ".");
	System.out.println("    Variable moduleName: string.");
	System.out.println("    Local Notation \"^ s\" := (moduleName -- s) (at level 0).");
        System.out.println("    Definition " + moduleName + " := MODULE {" + "\n");
        String prefix = "    ";
        for (BSVParser.ModulestmtContext modulestmt: ctx.modulestmt()) {
            System.out.print(prefix);
            visit(modulestmt);
            prefix = "    with ";
        }
        System.out.println("    }. (*" + ctx.moduleproto().name.getText() + " *)" + "\n");

	System.out.println(String.format("    Definition %s := (%s)%%kami.",
					 moduleName,
					 String.join("\n            ++ ", instances)));

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
	BSVParser.BsvtypeContext t = ctx.t;
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            System.out.print("        Let " + varName + ": " + bsvTypeToKami(t));
            BSVParser.ExpressionContext rhs = varinit.rhs;
            if (rhs != null) {
                System.out.print(" = ");
                visit(rhs);
            }
            System.out.println(". (* varbinding *)");
        }
        return null;
    }
    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVParser.ExpressionContext rhs = ctx.rhs;
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            System.out.print("        Let " + varName + ": " + bsvTypeToKami(entry.type) + " ");
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
        SymbolTableEntry entry = scope.lookup(varName);
        BSVType bsvtype = entry.type;
	InstanceNameVisitor inv = new InstanceNameVisitor(scope);
	String calleeInstanceName = inv.visit(ctx.rhs);
	if (calleeInstanceName != null && actionContext)
	    calleeInstanceName = calleeInstanceName.replace(".", "");

        if (typeName.startsWith("Reg")) {
            BSVType paramtype = bsvtype.params.get(0);
            System.out.print("Register ^\"" + varName + "\" : " + bsvTypeToKami(paramtype)
                             + " <- ");

            BSVParser.CallexprContext call = getCall(ctx.rhs);
            if (call != null && call.fcn != null && call.fcn.getText().equals("mkReg")) {
                System.out.print("$" + call.expression().get(0).getText());
            } else {
                visit(ctx.rhs);
            }

            System.out.println("");
        } else if (calleeInstanceName != null) {
	    System.out.println(String.format("        Call %s <- %s(); (* method call 1 *)", varName, calleeInstanceName));
	} else if (!actionContext) {
	    System.out.println(String.format("        (* instantiate %s *);", varName));

	    String instanceName = String.format("^%s", varName);
	    entry.instanceName = instanceName;

            BSVParser.CallexprContext call = getCall(ctx.rhs);
	    instances.add(call.fcn.getText());
	} else {
            System.out.print(String.format("        Call %s <- %s(", varName, calleeInstanceName));
	    System.err.println("generic call " + ctx.rhs.getRuleIndex() + " " + ctx.rhs.getText());
            BSVParser.CallexprContext call = getCall(ctx.rhs);
	    String sep = "";
	    for (BSVParser.ExpressionContext expr: call.expression()) {
		System.out.print(sep);
		visit(expr);
		sep = ", ";
	    }
	    System.out.println("); (* method call 2 *)");
        }
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
	boolean outerContext = actionContext;
	actionContext = true;
        scope = scopes.getScope(ruledef);
        String ruleName = ruledef.name.getText();
        RuleDef ruleDef = new RuleDef(ruleName);
        BSVParser.RulecondContext rulecond = ruledef.rulecond();
        moduleDef.addRule(ruleDef);

        System.out.println("Rule ^\"" + ruleName + "\" :=");
        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        if (rulecond != null) regReadVisitor.visit(rulecond);
        for (BSVParser.StmtContext stmt: ruledef.stmt()) {
            regReadVisitor.visit(stmt);
        }
        for (Map.Entry<String,BSVType> entry: regReadVisitor.regs.entrySet()) {
            String regName = entry.getKey();
            System.out.println("        Read " + regName + "_v : " + bsvTypeToKami(entry.getValue()) + " <- ^\"" + regName + "\";");
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
	actionContext = outerContext;
        return null;
    }

    @Override public Void visitMethoddef(BSVParser.MethoddefContext ctx) {
	boolean outerContext = actionContext;
	actionContext = true;

	SymbolTable methodScope = scopes.getScope(ctx);
	String methodName = ctx.name.getText();
	System.out.print("Method ^\"" + methodName + "\" (");
	if (ctx.methodformals() != null) {
	    String sep = "";
	    for (BSVParser.MethodformalContext formal: ctx.methodformals().methodformal()) {
		BSVParser.BsvtypeContext bsvtype = formal.bsvtype();
		String varName = formal.name.getText();
		System.out.print(sep + varName + ": " + bsvTypeToKami(bsvtype));
		sep = ", ";
	    }
	}
	String returntype = (ctx.bsvtype() != null) ? bsvTypeToKami(ctx.bsvtype()) : "";
	System.out.println(") : " + returntype + " := ");
	RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
	for (BSVParser.StmtContext stmt: ctx.stmt())
	    regReadVisitor.visit(stmt);
	if (ctx.expression() != null)
	    regReadVisitor.visit(ctx.expression());

        for (Map.Entry<String,BSVType> entry: regReadVisitor.regs.entrySet()) {
            String regName = entry.getKey();
            System.out.println("        Read " + regName + "_v : " + bsvTypeToKami(entry.getValue()) + " <- \"" + regName + "\";");
        }
	for (BSVParser.StmtContext stmt: ctx.stmt())
	    visit(stmt);
	if (ctx.expression() != null)
	    visit(ctx.expression());

	if (returntype.equals("Action"))
	    System.out.println("        Retv");
	System.out.println("");
	actionContext = outerContext;
	return null;
    }

    @Override public Void visitRegwrite(BSVParser.RegwriteContext regwrite) {
        System.out.print("        Write ^\"");
        visit(regwrite.lhs);
        System.out.print("\"");
	String regName = regwrite.lhs.getText();
	SymbolTableEntry entry = scope.lookup(regName);
	if (entry != null) {
	    System.out.print(" : ");
	    System.out.print(bsvTypeToKami(entry.type.params.get(0)));
	}
	System.out.print(" <- ");
        visit(regwrite.rhs);
        System.out.println(";");
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
        System.out.println(";");
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
    @Override public Void visitReturnexpr(BSVParser.ReturnexprContext ctx) {
	System.out.print("        Ret ");
	visit(ctx.expression());
	System.out.println("");
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
                    System.out.print("#" + varName);
            } else {
                System.out.print("#" + varName);
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

    @Override public Void visitCallexpr(BSVParser.CallexprContext ctx) {
	InstanceNameVisitor inv = new InstanceNameVisitor(scope);
	String methodName = inv.visit(ctx.fcn);
	methodName = methodName.replace(".", "");
	if (methodName != null) {
	    System.out.print(String.format("        Call %s(", methodName));
	    String sep = "";
	    for (BSVParser.ExpressionContext expr: ctx.expression()) {
		System.out.print(sep);
		visit(expr);
		sep = ", ";
	    }
	    System.out.println("); (* method call expr *)");
	} else {
	    System.err.println(String.format("How to call action function {%s}", ctx.fcn.getText()));
	}
	return null;
    }

    public String bsvTypeToKami(BSVType t) {
	return bsvTypeToKami(t, 0);
    }
    public String bsvTypeToKami(BSVType t, int level) {
        if (t == null)
            return "<nulltype>";
        t = t.prune();
        String kamitype = t.name;
	if (kamitype.equals("Action"))
	    kamitype = "Void";
        for (BSVType p: t.params)
            kamitype += " " + bsvTypeToKami(p);
	if (level > 0)
	    kamitype = String.format("&%s)", kamitype);
        return kamitype;
    }
    public String bsvTypeToKami(BSVParser.BsvtypeContext t) {
	return bsvTypeToKami(t, 0);
    }
    public String bsvTypeToKami(BSVParser.BsvtypeContext t, int level) {
        if (t == null)
            return "<nulltype>";
	if (t.typeide() != null) {
	    String kamitype = t.typeide().getText();
	    if (kamitype.equals("Action"))
		kamitype = "Void";
	    for (BSVParser.BsvtypeContext p: t.bsvtype())
		kamitype += " " + bsvTypeToKami(p, 1);
	    if (level > 0)
		kamitype = String.format("(%s)", kamitype);
	    return kamitype;
	} else if (t.typenat() != null) {
	    return t.getText();
	} else {
	    return "<functionproto>";
	}
    }
}
