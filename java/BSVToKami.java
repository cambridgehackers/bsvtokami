import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;

public class BSVToKami extends BSVBaseVisitor<Void>
{
    private final StaticAnalysis scopes;
    private SymbolTable scope;
    BSVToKami(StaticAnalysis scopes) {
	this.scopes = scopes;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
	scope = scopes.getScope(ctx);
	System.out.println("Definition " + ctx.moduleproto().modulename.getText() + " := MODULE {" + "\n");
	visitChildren(ctx);
	System.out.println("}. (*" + ctx.moduleproto().modulename.getText() + " *)" + "\n");
	scope = scope.parent;
	return null;
    }

    BSVParser.ExprprimaryContext getCall(ParserRuleContext ctx) {
	switch (ctx.getRuleIndex()) {
	case BSVParser.RULE_expression: {
	    BSVParser.OperatorExprContext ec = (BSVParser.OperatorExprContext)ctx;
	    return getCall(ec.binopexpr());
	}
	case BSVParser.RULE_binopexpr: {
	    BSVParser.BinopexprContext bc = (BSVParser.BinopexprContext)ctx;
	    return getCall(bc.unopexpr());
	}
	case BSVParser.RULE_unopexpr: {
	    BSVParser.UnopexprContext uc = (BSVParser.UnopexprContext)ctx;
	    return getCall(uc.exprprimary());
	}
	case BSVParser.RULE_exprprimary: {
	    BSVParser.ExprprimaryContext ep = (BSVParser.ExprprimaryContext)ctx;
	    if (ep.fcn != null) {
		return ep;
	    } else {
		return null;
	    }
	}
	}
	return null;
    }

    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
	String typeName = ctx.t.getText();
	for (BSVParser.VarinitContext varinit: ctx.varinit()) {
	    String varName = varinit.var.getText();
	    System.out.println("    Variable " + varName + ": " + typeName + ".");
	}	
	return null;
    }
    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
	String varName = ctx.var.getText();
	System.out.println("    Variable " + varName + ": " + "TBDLetType" + ".");
	return null ;
    }
    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
	String typeName = ctx.t.getText();
	String varName = ctx.var.getText();
	if (typeName.startsWith("Reg")) {
	    System.out.print("    Register \"" + varName + "\" : " + "TBDType"
			     + " <- ");
	    
	    BSVParser.ExprprimaryContext call = getCall(ctx.rhs);
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
	System.out.println("    with Rule \"" + ruledef.rulename.getText() + "\" :=" + "\n");
	visitChildren(ruledef);
	System.out.println("        Retv (* rule " + ruledef.rulename.getText() + " *)" + "\n");
	scope = scope.parent;
	return null;
    }
    @Override public Void visitRegwrite(BSVParser.RegwriteContext regwrite) {
	System.out.print("        WriteReg ");
	visitChildren(regwrite.lhs);
	System.out.print(" <- ");
	visitChildren(regwrite.rhs);
	System.out.println(";" + "\n");
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
    @Override public Void visitExprprimary(BSVParser.ExprprimaryContext ctx) {
	if (ctx.val != null) {
	    String varName = ctx.val.getText();
	    if (scope.containsKey(varName)) {
		SymbolTableEntry entry = scope.lookup(varName);
		//System.err.println("found binding " + varName + " " + entry.type);
		if (entry.type.equals("Reg"))
		    System.out.print("(ReadReg " + varName + ")");
		else
		    System.out.print(varName);
	    } else {
		System.out.print(varName);
	    }
	}
	return null;
    }

}
