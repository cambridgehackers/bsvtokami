import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private String packageName;
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;
    private HashMap<String, SymbolTable> packages;
    private BSVTypeVisitor typeVisitor;

    StaticAnalysis() {
        scopes = new HashMap<ParserRuleContext, SymbolTable>();
        packages = new HashMap<String, SymbolTable>();
        typeVisitor = new BSVTypeVisitor();
	symbolTable = new SymbolTable(null, SymbolTable.ScopeType.Package, "Global");
        typeVisitor.pushScope(symbolTable);
    }

    public void visitPackage(String packageName, ParserRuleContext ctx) {
        this.packageName = packageName;
        visit(ctx);
    }

    private void importPackage(String pkgname) {
        SymbolTable importScope = symbolTable.parent;
        SymbolTable pkgscope = packages.get(pkgname);
        if (pkgscope == null) {
            System.err.println(String.format("Failed to import package %s", pkgname));
            return;
        }
        System.err.println(String.format("Importing package %s", pkgname));
        for (Map.Entry<String,SymbolTableEntry> entry: pkgscope.bindings.entrySet()) {
            System.err.println(String.format("Importing %s::%s entry %s", pkgname, entry.getKey(), entry.getValue()));
            importScope.bind(entry.getKey(), entry.getValue());
        }
        for (Map.Entry<String,SymbolTableEntry> entry: pkgscope.typeBindings.entrySet()) {
            System.err.println(String.format("Importing %s::%s entry %s", pkgname, entry.getKey(), entry.getValue()));
            importScope.bindType(entry.getKey(), entry.getValue());
        }
    }

    private void pushScope(ParserRuleContext ctx, SymbolTable.ScopeType st, String name) {
        symbolTable = new SymbolTable(symbolTable, st, name);
        System.err.println("pushScope { " + name + "-" + symbolTable + " " + st);
        scopes.put(ctx, symbolTable);
        typeVisitor.pushScope(symbolTable);
    }

    private void popScope() {
	assert symbolTable.parent != null : String.format("Symbol table %s:%s has no parent", symbolTable.name, symbolTable);
        System.err.println(String.format("popScope %s-%s parent %s-%s }",
					 symbolTable.name, symbolTable, symbolTable.parent.name, symbolTable.parent));
	assert typeVisitor != null;
        typeVisitor.popScope();
        symbolTable = symbolTable.parent;
    }

    private boolean isModuleContext() {
        SymbolTable s = symbolTable;
        while (s != null) {
            if (s.scopeType == SymbolTable.ScopeType.Module) {
                return true;
            } else if (s.scopeType == SymbolTable.ScopeType.Block) {
                s = s.parent;
            } else {
                return false;
            }
        }
        return false;
    }
    private boolean isActionContext() {
        SymbolTable s = symbolTable;
        while (s != null) {
            if (s.scopeType == SymbolTable.ScopeType.Action) {
                return true;
            } else if (s.scopeType == SymbolTable.ScopeType.Block) {
                s = s.parent;
            } else {
                return false;
            }
        }
        return false;
    }
    SymbolTable getScope(ParserRuleContext def) {
        if (scopes.containsKey(def)) {
            return (SymbolTable)scopes.get(def);
        } else {
            return null;
        }
    }

    SymbolTableEntry lookup(String packageName, String varName) {
        assert packages.containsKey(packageName);
        SymbolTable packageScope = packages.get(packageName);
        return packageScope.lookup(varName);
    }

    public static String unescape(String identifier) {
	if (identifier.startsWith("\\"))
	    return identifier.substring(1);
	else
	    return identifier;
    }

    public static String unescape(ParserRuleContext ctx) {
	String identifier = ctx.getText();
	return unescape(identifier);
    }

    @Override public Void visitPackagedef(BSVParser.PackagedefContext ctx) {
        pushScope(ctx, SymbolTable.ScopeType.Package, packageName);
        importPackage("Prelude");
        packages.put(packageName, symbolTable);
        visitChildren(ctx);
        popScope();
        return null;
    }

    @Override public Void visitImportdecl(BSVParser.ImportdeclContext importdecl) {
        for (BSVParser.ImportitemContext importitem: importdecl.importitem()) {
            String importedPkgName = importitem.pkgname.getText();
            importPackage(importedPkgName);
        }
        return null;
    }

    @Override
    public Void visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {
        String interfaceName = ctx.typedeftype().typeide().getText();
        System.err.println("entering interface decl " + interfaceName + " {");
        pushScope(ctx, SymbolTable.ScopeType.Declaration, interfaceName);
        BSVType interfaceType = typeVisitor.visit(ctx.typedeftype());
        SymbolTable interfaceMappings = symbolTable;

        visitChildren(ctx);

        popScope();
	for (Map.Entry<String,SymbolTableEntry> mapping: interfaceMappings.bindings.entrySet()) {
	    System.err.println(String.format("interface mapping  %s  %s : %s", interfaceName, mapping.getKey(), mapping.getValue().type));
	}
	for (Map.Entry<String,SymbolTableEntry> mapping: interfaceMappings.typeBindings.entrySet()) {
	    System.err.println(String.format("interface tmapping %s  %s : %s", interfaceName, mapping.getKey(), mapping.getValue().type));
	}
        symbolTable.bindType(packageName, interfaceName, interfaceType, interfaceMappings);

        System.err.println("} exiting interface decl " + interfaceName);
        return null;
    }

    @Override public Void visitSubinterfacedecl(BSVParser.SubinterfacedeclContext ctx) {
        String subinterfaceName = ctx.lowerCaseIdentifier().getText();
        System.err.println("entering subinterface decl " + subinterfaceName + " {");

        BSVType subinterfaceType = typeVisitor.visit(ctx.bsvtype());

        symbolTable.bind(subinterfaceName, subinterfaceType);

        System.err.println("} exiting sub interface decl " + subinterfaceName);
        return null;
    }

    @Override public Void visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        String typedefname = ctx.upperCaseIdentifier().getText();
        BSVType enumtype = new BSVType(typedefname);
        symbolTable.bind(packageName, typedefname,
                         new SymbolTableEntry(typedefname,
                                              enumtype));
        for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String tagname = elt.upperCaseIdentifier().getText();
            symbolTable.bind(packageName, tagname, new SymbolTableEntry(tagname, enumtype));
	    System.err.println(String.format("Enum tag %s : %s", tagname, enumtype));
        }
        return null;
    }

    @Override public Void visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        String typedefname = ctx.typedeftype().getText();
	typeVisitor.visit(ctx);
        return null;
    }

    @Override public Void visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        String typedefname = ctx.typedeftype().typeide().getText();
        BSVType taggeduniontype = typeVisitor.visit(ctx);
        symbolTable.bind(packageName, typedefname,
                         new SymbolTableEntry(typedefname,
                                              taggeduniontype));
	System.err.println(String.format("tagged union %s : %s", typedefname, taggeduniontype));
        for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
            BSVParser.UpperCaseIdentifierContext id = member.upperCaseIdentifier();
            if (id != null) {
                String idname = id.getText();
                symbolTable.bind(packageName, idname, new SymbolTableEntry(idname, taggeduniontype));
		System.err.println(String.format("tagged union member %s : %s", idname, taggeduniontype));
            } else if (member.substruct() != null) {
            } else if (member.subunion() != null) {
            }
        }
        return null;
    }

    @Override public Void visitTypeclassdecl(BSVParser.TypeclassdeclContext ctx) {
	for (BSVParser.OverloadeddeclContext def : ctx.overloadeddecl()) {
	    BSVParser.FunctionprotoContext functionproto = def.functionproto();
	    BSVParser.ModuleprotoContext moduleproto = def.moduleproto();
	    BSVParser.VardeclContext vardecl = def.vardecl();
	    if (ctx.provisos() != null)
		visit(ctx.provisos());
	    if (functionproto != null)
		visit(functionproto);
	    if (moduleproto != null)
		visit(moduleproto);
	    if (vardecl != null)
		visit(vardecl);
	}

        return null;
    }

    @Override public Void visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) {
	for (BSVParser.OverloadeddefContext def : ctx.overloadeddef()) {
	    BSVParser.FunctiondefContext functiondef = def.functiondef();
	    BSVParser.ModuledefContext moduledef = def.moduledef();
	    BSVParser.VarassignContext varassign = def.varassign();
	    // Add a scope to catch the symbol table entry
	    pushScope(ctx, SymbolTable.ScopeType.TypeClassInstance, ctx.typeclasside(0).getText());

	    if (ctx.provisos() != null)
		visit(ctx.provisos());
	    if (functiondef != null)
		visit(functiondef);
	    if (moduledef != null)
		visit(moduledef);
	    if (varassign != null)
		visit(varassign);

	    for (Map.Entry<String,SymbolTableEntry> ste: symbolTable.bindings.entrySet()) {
		String instanceName = ste.getKey();
		SymbolTableEntry instanceEntry = ste.getValue();
		SymbolTableEntry classEntry = symbolTable.lookup(instanceName);
		assert classEntry != null : String.format("Instance var %s", instanceName);
		System.err.println(String.format("Adding instance %s : %s", instanceName, instanceEntry.type));
		classEntry.addInstance(instanceEntry);
	    }
	    popScope();
	}

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
        symbolTable.bind(packageName, typedefname,
                         new SymbolTableEntry(typedefname, bsvtype));
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        String modulename = ctx.moduleproto().name.getText();
        BSVType moduletype = typeVisitor.visit(ctx.moduleproto());
        System.err.println(String.format("Binding module %s", modulename));
        symbolTable.bind(packageName, modulename,
                         new SymbolTableEntry(modulename, moduletype));
        pushScope(ctx, SymbolTable.ScopeType.Module, modulename);
	if (ctx.moduleproto().provisos() != null)
	    visit(ctx.moduleproto().provisos());

	BSVParser.MethodprotoformalsContext formals = ctx.moduleproto().methodprotoformals();
	if (formals != null) {
	    for (BSVParser.MethodprotoformalContext formal : formals.methodprotoformal()) {
		if (formal.bsvtype() != null) {
		    BSVType bsvtype = typeVisitor.visit(formal.bsvtype());
		    String name = formal.name.getText();
		    symbolTable.bind(name, bsvtype);
		} else {
		    assert formal.functionproto() != null;
		    BSVType bsvtype = typeVisitor.visit(formal.functionproto());
		    String name = formal.functionproto().name.getText();
		    symbolTable.bind(name, bsvtype);
		}
	    }
	}

	for (BSVParser.ModulestmtContext stmt : ctx.modulestmt())
	    visit(stmt);

        popScope();
        return null;
    }

    @Override public Void visitImportbvi(BSVParser.ImportbviContext ctx) {
        String modulename = ctx.moduleproto().name.getText();
        BSVType moduletype = typeVisitor.visit(ctx.moduleproto());
        System.err.println(String.format("Binding import BVI module %s", modulename));
        symbolTable.bind(packageName, modulename,
                         new SymbolTableEntry(modulename, moduletype));
	return null;
    }

    @Override public Void visitMethoddef(BSVParser.MethoddefContext ctx) {
        String methodName = ctx.name.getText();
        System.err.println("entering methoddef " + methodName + " {");
        BSVType methodType = new BSVType(); // FIXME
        symbolTable.bind(methodName, new SymbolTableEntry(methodName, methodType));
        pushScope(ctx, SymbolTable.ScopeType.Action, methodName);

        if (ctx.methodformals() != null) {
            for (BSVParser.MethodformalContext methodformal: ctx.methodformals().methodformal()) {
                // FIXME: if type is not here, get it from the interface decl
                BSVType mftype;
                String mfname;
                if (methodformal.functionproto() != null) {
                    mftype = typeVisitor.visit(methodformal.functionproto());
                    mfname = methodformal.functionproto().name.getText();
                } else {
                    mftype = (methodformal.bsvtype() != null) ? typeVisitor.visit(methodformal.bsvtype()) : new BSVType();
                    mfname = methodformal.name.getText();
                }
                symbolTable.bind(methodformal.lowerCaseIdentifier().getText(), new SymbolTableEntry(mfname, mftype));
            }
        }
        if (ctx.methodcond() != null)
            visit(ctx.methodcond());
	if (ctx.provisos() != null)
	    visit(ctx.provisos());
        for (BSVParser.StmtContext stmt: ctx.stmt())
            visit(stmt);
        if (ctx.expression() != null)
            visit(ctx.expression());
        popScope();
        System.err.println("} exiting methoddef " + methodName);
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
        String ruleName = (ruledef.name != null) ? ruledef.name.getText() : "<anonrule>";
        System.err.println("entering rule " + ruleName + " {");
        pushScope(ruledef, SymbolTable.ScopeType.Action, ruleName);
        visitChildren(ruledef);
        popScope();
        System.err.println("} exited rule " + ruleName);
        return null;
    }
    @Override public Void visitStmt(BSVParser.StmtContext ctx) {
        System.err.println("visit stmt");
        return visitChildren(ctx);
        //System.err.println("unhandled visitStmt " + ctx.getText());
        //return null;
    }
    @Override public Void visitMethodproto(BSVParser.MethodprotoContext ctx) {
        String methodname = ctx.name.getText();
        pushScope(ctx, SymbolTable.ScopeType.Declaration, methodname);
        BSVType methodtype = typeVisitor.visit(ctx);
        popScope();
        symbolTable.bind(methodname, new SymbolTableEntry(methodname, methodtype));
        return null;
    }
 
    @Override public Void visitModuleproto(BSVParser.ModuleprotoContext moduleproto) {
        String modulename = unescape(moduleproto.name.getText());
        BSVType moduletype = typeVisitor.visit(moduleproto);
        if (symbolTable.scopeType == SymbolTable.ScopeType.Package) {
            symbolTable.bind(packageName, modulename,
                             new SymbolTableEntry(modulename, moduletype));
        } else {
            symbolTable.bind(modulename,
                             new SymbolTableEntry(modulename, moduletype));
        }
	return null;
    }

    @Override public Void visitFunctionproto(BSVParser.FunctionprotoContext functionproto) {
        String functionname = unescape(functionproto.name.getText());
        BSVType functiontype = typeVisitor.visit(functionproto);
        if (symbolTable.scopeType == SymbolTable.ScopeType.Package) {
            symbolTable.bind(packageName, functionname,
                             new SymbolTableEntry(functionname, functiontype));
        } else {
            symbolTable.bind(functionname,
                             new SymbolTableEntry(functionname, functiontype));
        }
	return null;
    }

    @Override public Void visitFunctiondef(BSVParser.FunctiondefContext ctx) {
        BSVParser.FunctionprotoContext functionproto = ctx.functionproto();
        System.err.println("visit functiondef " + functionproto);
        String functionname = functionproto.name.getText();
	visit(functionproto);
        System.err.println(String.format("entering functiondef %s {", functionname));
        // save the lexical scope
        pushScope(ctx, SymbolTable.ScopeType.Action, functionname);
	if (ctx.functionproto().provisos() != null)
	    visit(ctx.functionproto().provisos());
	if (functionproto.methodprotoformals() != null) {
	    for (BSVParser.MethodprotoformalContext formal: functionproto.methodprotoformals().methodprotoformal()) {
		visit(formal);
	    }
	}
        visit(functionproto);
        if (ctx.expression() != null)
            visit(ctx.expression());
        for (BSVParser.StmtContext stmt: ctx.stmt())
            visit(stmt);
        popScope();
        System.err.println("} exiting functiondef " + functionname);
        return null;
    }
    @Override public Void visitMethodprotoformal(BSVParser.MethodprotoformalContext ctx) {
        if (ctx.functionproto() != null) {
            BSVParser.FunctionprotoContext functionproto = ctx.functionproto();
            BSVType bsvtype = typeVisitor.visit(functionproto);
            String varname = functionproto.name.getText();
            symbolTable.bind(varname, new SymbolTableEntry(varname, bsvtype));
        } else if (ctx.bsvtype() != null) {
            BSVType bsvtype = typeVisitor.visit(ctx.bsvtype());
            String varname = ctx.lowerCaseIdentifier().getText();
	    System.err.println(String.format("binding methodproto formal %s : %s", varname, bsvtype));
            symbolTable.bind(varname, new SymbolTableEntry(varname, bsvtype));
        }
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
            if (symbolTable.scopeType == SymbolTable.ScopeType.Package) {
                symbolTable.bind(packageName, varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
            } else {
                symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
            }
        }
        return null;
    }

    void handleArrowBinding(String varName, BSVType lhsparamtype, BSVType rhstype,
                            ParserRuleContext lhs, ParserRuleContext rhs) {
        if (varName == null || lhsparamtype == null || rhstype == null) {
            System.err.println(String.format("varName=%s lhsparamtype=%s rhstype=%s\n",
                                             varName, lhsparamtype, rhstype));
            return;
        }

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
        BSVType lhstype = typeVisitor.visit(ctx.t);
        BSVType rhstype = typeVisitor.visit(ctx.rhs);
        String varName = ctx.var.getText();
        handleArrowBinding(varName, lhstype, rhstype, ctx.var, ctx.rhs);
        SymbolTableEntry entry = new SymbolTableEntry(varName, lhstype.prune());
        if (isModuleContext()) {
            entry.instanceName = String.format("%s", varName);
        }
        assert (symbolTable.scopeType != SymbolTable.ScopeType.Package);
        symbolTable.bind(varName, entry);
        return null;
    }

    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVType rhstype = typeVisitor.visit(ctx.rhs);
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            System.err.println("Let " + varName + " : " + rhstype + " " + ctx.op.getText() + " " + ctx.rhs.getText());
            BSVType lhstype = rhstype;
            boolean arrowBinding = ctx.op.getText().equals("<-");
            if (arrowBinding) {
                lhstype = new BSVType();
                handleArrowBinding(varName, lhstype, rhstype, ident, ctx.rhs);
            }
            SymbolTableEntry entry = new SymbolTableEntry(varName, lhstype.prune());
            if (isModuleContext() && arrowBinding) {
                entry.instanceName = String.format("%s", varName);
            }
            if (symbolTable.scopeType == SymbolTable.ScopeType.Package) {
                symbolTable.bind(packageName, varName, entry);
            } else {
                symbolTable.bind(varName, entry);
            }
        }
        return null;
    }
    @Override public Void visitRegwrite(BSVParser.RegwriteContext ctx) {
        BSVType lhstype = typeVisitor.visit(ctx.lhs);
        BSVType rhstype = typeVisitor.visit(ctx.rhs);
        BSVType rhsregtype = new BSVType("Reg", rhstype);
	assert lhstype != null : ctx.lhs.getText();
	assert rhstype != null : ctx.rhs.getText();
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
        System.err.println("entering block {");
        pushScope(block, symbolTable.scopeType, "begin");

        visitChildren(block);

        popScope();
        System.err.println("} exited block");
        return null;
    }
    @Override public Void visitOperatorExpr(BSVParser.OperatorExprContext ctx) {
        typeVisitor.visit(ctx.binopexpr());
        return null;
    }

    @Override public Void visitProvisos(BSVParser.ProvisosContext ctx) {
	return visitChildren(ctx);
    }

    private void bindFreeTypeVars(BSVType t) {
	System.err.println(String.format("bindFreeTypeVars %s %s entry %s", t, t.isVar, symbolTable.lookupType(t.name)));
	if (t.isVar) {
	    SymbolTableEntry entry = symbolTable.lookupType(t.name);
	    if (entry == null) {
		symbolTable.bindType(t.name, t);
	    }
	} else {
	    for (BSVType p : t.params) {
		bindFreeTypeVars(p);
	    }
	}
    }

    @Override public Void visitProviso(BSVParser.ProvisoContext proviso) {
	System.err.println("visiting proviso " + proviso.getText());
	String varName = proviso.var.getText();
	for (BSVParser.BsvtypeContext t : proviso.bsvtype()) {
	    BSVType bsvtype = typeVisitor.visit(t);
	    bindFreeTypeVars(bsvtype);
	}
	return null;
    }

}
