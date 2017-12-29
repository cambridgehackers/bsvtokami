import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;
    
    StaticAnalysis() {
	// global table
	symbolTable = new SymbolTable(null);
	scopes = new HashMap<ParserRuleContext, SymbolTable>();
    }

    SymbolTable getScope(ParserRuleContext def) {
	if (scopes.containsKey(def)) {
	    return (SymbolTable)scopes.get(def);
	} else {
	    return null;
	}
    }	

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
	symbolTable = new SymbolTable(symbolTable);
	scopes.put(ctx, symbolTable);
	visitChildren(ctx);
	symbolTable = symbolTable.parent;
	return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
	symbolTable = new SymbolTable(symbolTable);
	scopes.put(ruledef, symbolTable);
	visitChildren(ruledef);
	symbolTable = symbolTable.parent;
	return null;
    }


    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
	String typeName = ctx.t.getText();
	for (BSVParser.VarinitContext varinit: ctx.varinit()) {
	    String varName = varinit.var.getText();
	    //System.err.println("VarInit " + typeName + " " + varName);
	    symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, typeName));
	}
	return null;
    }

    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
	String typeName = ctx.t.getText();
	String varName = ctx.var.getText();
	//System.err.println("ActionBinding " + typeName + " " + varName);
	symbolTable.bind(ctx.var.getText(), new SymbolTableEntry(varName, typeName));
	return null;
    }


}
