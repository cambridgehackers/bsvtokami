import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;
    private BSVTypeVisitor typeVisitor;

    StaticAnalysis() {
        // global table
        symbolTable = new SymbolTable(null, SymbolTable.ScopeType.Package);
        scopes = new HashMap<ParserRuleContext, SymbolTable>();
	typeVisitor = new BSVTypeVisitor();
	typeVisitor.pushScope(symbolTable);
    }

    private void pushScope(ParserRuleContext ctx, SymbolTable.ScopeType st) {
        symbolTable = new SymbolTable(symbolTable, st);
        scopes.put(ctx, symbolTable);
	typeVisitor.pushScope(symbolTable);
    }

    private void popScope() {
	typeVisitor.popScope();
	symbolTable = symbolTable.parent;
    }

    SymbolTable getScope(ParserRuleContext def) {
        if (scopes.containsKey(def)) {
            return (SymbolTable)scopes.get(def);
        } else {
            return null;
        }
    }

    @Override
    public Void visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {
        String interfaceName = ctx.typedeftype().typeide().getText();
        symbolTable.bind(interfaceName,
                         new SymbolTableEntry(interfaceName,
					      typeVisitor.visit(ctx.typedeftype())));

	pushScope(ctx, SymbolTable.ScopeType.Declaration);

        visitChildren(ctx);

	popScope();
        return null;
    }

    @Override public Void visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        String typedefname = ctx.upperCaseIdentifier().getText();
	BSVType enumtype = typeVisitor.visit(ctx);
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname,
					      enumtype));
        for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String tagname = elt.upperCaseIdentifier().getText();
            symbolTable.bind(tagname, new SymbolTableEntry(tagname, enumtype));
        }
        return null;
    }

    @Override public Void visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        String typedefname = ctx.typedeftype().getText();
        return null;
    }

    @Override public Void visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        String typedefname = ctx.typedeftype().typeide().getText();
	BSVType taggeduniontype = typeVisitor.visit(ctx);
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname,
					      taggeduniontype));
        for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
            BSVParser.UpperCaseIdentifierContext id = member.upperCaseIdentifier();
            if (id != null) {
                String idname = id.getText();
                symbolTable.bind(idname, new SymbolTableEntry(idname, taggeduniontype));
            } else if (member.substruct() != null) {
            } else if (member.subunion() != null) {
            }
        }
        return null;
    }

    @Override public Void visitTypeclassdecl(BSVParser.TypeclassdeclContext ctx) {
	pushScope(ctx, SymbolTable.ScopeType.Declaration);

        visitChildren(ctx);

	popScope();
        return null;
    }

    @Override public Void visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) {
        pushScope(ctx, SymbolTable.ScopeType.Declaration);

        visitChildren(ctx);

	popScope();
        return null;
    }

    @Override
    public Void visitTypedefsynonym(BSVParser.TypedefsynonymContext ctx) {
        String typedefname = ctx.typedeftype().typeide().getText();
        BSVType bsvtype;
        if (ctx.bsvtype() != null)
            bsvtype = typeVisitor.visit(ctx.bsvtype());
        else
            bsvtype = typeVisitor.visit(ctx.functionproto());
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname, bsvtype));
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        String modulename = ctx.moduleproto().name.getText();
        BSVType moduletype = typeVisitor.visit(ctx.moduleproto());
        symbolTable.bind(modulename,
                         new SymbolTableEntry(modulename, moduletype));
        pushScope(ctx, SymbolTable.ScopeType.Module);

        visitChildren(ctx);

	popScope();
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
        pushScope(ruledef, SymbolTable.ScopeType.Action);

	System.err.println("entering rule {");
        visitChildren(ruledef);
	System.err.println("} exited rule");

	popScope();
        return null;
    }

    @Override public Void visitMethodproto(BSVParser.MethodprotoContext ctx) {
	pushScope(ctx, SymbolTable.ScopeType.Declaration);
	BSVType methodtype = typeVisitor.visit(ctx);
	popScope();
	return null;
    }

    @Override public Void visitFunctiondef(BSVParser.FunctiondefContext ctx) {
	BSVParser.FunctionprotoContext functionproto = ctx.functionproto();
	BSVType functiontype = typeVisitor.visit(functionproto);
	String functionname = functionproto.name.getText();
	symbolTable.bind(functionname,
			 new SymbolTableEntry(functionname, functiontype));
	return null;
    }
    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
	BSVType bsvtype = typeVisitor.visit(ctx.t);
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
	    if (varinit.rhs != null) {
		BSVType rhstype = typeVisitor.visit(varinit.rhs);
		try {
		    bsvtype.unify(rhstype);
		} catch (InferenceError e) {
		    System.err.println("Var binding InferenceError " + e);
		}
	    }
            //System.err.println("VarInit " + typeName + " " + varName);
            symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
        }
        return null;
    }

    void handleArrowBinding(String varName, BSVType lhsparamtype, BSVType rhstype) {
	BSVType lhstype = new BSVType((symbolTable.scopeType == SymbolTable.ScopeType.Module)
				      ? "Module" : "ActionValue",
				      lhsparamtype);
	try {
	    lhstype.unify(rhstype);
	} catch (InferenceError e) {
	    System.err.println("Action binding InferenceError " + e);
	}
        System.err.println("ArrowBinding  " + varName + " : " + lhsparamtype);
	System.err.println("    bsvtype (" + lhstype + ") rhstype (" + rhstype + ")");
    }

    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
	BSVType bsvtype = typeVisitor.visit(ctx.t);
	BSVType rhstype = typeVisitor.visit(ctx.rhs);
	String varName = ctx.var.getText();
	handleArrowBinding(ctx.var.getText(), bsvtype, rhstype);
        symbolTable.bind(ctx.var.getText(), new SymbolTableEntry(varName, bsvtype.prune()));
        return null;
    }

    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVType rhstype = typeVisitor.visit(ctx.rhs);
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            System.err.println("Let " + varName + " : " + rhstype + " " + ctx.op.getText() + " " + ctx.rhs.getText());
	    BSVType lhstype = rhstype;
	    if (ctx.op.getText().equals("<-")) {
		lhstype = new BSVType();
		handleArrowBinding(varName, lhstype, rhstype);
	    }
            symbolTable.bind(varName, new SymbolTableEntry(varName, lhstype));
        }
        return null;
    }
    @Override public Void visitRegwrite(BSVParser.RegwriteContext ctx) {
	BSVType lhstype = typeVisitor.visit(ctx.lhs);
	BSVType rhstype = typeVisitor.visit(ctx.rhs);
	BSVType rhsregtype = new BSVType("Reg", rhstype);
	try {
	    System.err.println("lhs " + ctx.lhs.getText() + " : " + lhstype.prune());
	    System.err.println("rhs " + ctx.rhs.getText() + " : " + rhstype.prune());
	    lhstype.unify(rhsregtype);
	    System.err.println("regwrite lhs (" + lhstype + ") rhs (" + rhstype + ")");
	} catch (InferenceError e) {
	    System.err.println("Reg write InferenceError " + e);
	}
	return null;
    }
    @Override public Void visitBeginendblock(BSVParser.BeginendblockContext block) {
        pushScope(block, symbolTable.scopeType);

	System.err.println("entering block {");
        visitChildren(block);
	System.err.println("} exited block");

	popScope();
	return null;
    }
}
