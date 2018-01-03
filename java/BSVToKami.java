import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;

class BSVExpressionConverter extends BSVBaseVisitor<Expression>
{
	@Override
	public Expression visitIdentifier(BSVParser.IdentifierContext ctx) {
	    return new VariableRead(ctx.getText());
	}
	@Override
	public Expression visitCondExpr(BSVParser.CondExprContext ctx) {
	    return new CondExpression(visit(ctx.condpredicate()),
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
	if (ctx.packagedecl() != null) {
	    if (!pkgName.equals(ctx.packagedecl().pkgname)) {
		System.err.println("Expected " + pkgName + " found " + ctx.packagedecl().pkgname);
	    }
	}
	return visitChildren(ctx);
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
	scope = scopes.getScope(ctx);
	String moduleName = ctx.moduleproto().modulename.getText();
	moduleDef = new ModuleDef(moduleName);
	pkg.addStatement(moduleDef);
	System.out.println("Definition " + moduleName + " := MODULE {" + "\n");
	visitChildren(ctx);
	System.out.println("}. (*" + ctx.moduleproto().modulename.getText() + " *)" + "\n");
	scope = scope.parent;
	moduleDef = null;
	return null;
    }

    BSVParser.CallexprContext getCall(ParserRuleContext ctx) {
	//FIXME: use type info
	return null;
    }

    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
	String typeName = ctx.t.getText();
	for (BSVParser.VarinitContext varinit: ctx.varinit()) {
	    String varName = varinit.var.getText();
	    System.out.println("    Variable " + varName + ": " + typeName + ".");
	    BSVParser.ExpressionContext rhs = varinit.rhs;
	    Expression expr = expressionConverter.visit(rhs);
	}	
	return null;
    }
    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
	String varName = ctx.var.getText();
	BSVParser.ExpressionContext rhs = ctx.rhs;
	System.out.println("    Variable " + varName + ": " + "TBDLetType" + ".");
	Expression expr = expressionConverter.visit(rhs);
	return null ;
    }
    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
	String typeName = ctx.t.getText();
	String varName = ctx.var.getText();
	BSVParser.ExpressionContext rhs = ctx.rhs;
	Expression expr = expressionConverter.visit(rhs);
	if (typeName.startsWith("Reg")) {
	    System.out.print("    Register \"" + varName + "\" : " + "TBDType"
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
	String ruleName = ruledef.rulename.getText();
	RuleDef ruleDef = new RuleDef(ruleName);
	BSVParser.RulecondContext rulecond = ruledef.rulecond();
	moduleDef.addRule(ruleDef);

	System.out.println("    with Rule \"" + ruleName + "\" :=" + "\n");
	if (rulecond != null) {
	    System.out.print("        Assert(");
	    visit(rulecond);
	    System.out.println(")");
	}
	visit(ruledef.rulebody());
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

    @Override
    public Void visitPattern(BSVParser.PatternContext ctx) {
	//FIXME
	System.out.print("$" + ctx.getText());
	return null;
    }

    @Override
    public Void visitCondpredicate(BSVParser.CondpredicateContext ctx) {
	visit(ctx.expression());
	if (ctx.pattern() != null) {
	    System.out.print(" matches ");
	    visit(ctx.pattern());
	}
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
	    System.err.println("var " + varName);
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
