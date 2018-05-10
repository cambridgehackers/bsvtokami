package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.util.logging.Logger;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private String packageName;
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;
    private HashMap<String, SymbolTable> packages;
    private Stack<SymbolTable> scopeStack = new Stack<>();
    private Stack<ParserRuleContext> ctxStack = new Stack<>();
    private BSVTypeVisitor typeVisitor;
    private boolean declOnly;
    private static Logger logger = Logger.getGlobal();

    StaticAnalysis() {
        scopes = new HashMap<ParserRuleContext, SymbolTable>();
        packages = new HashMap<String, SymbolTable>();
        typeVisitor = new BSVTypeVisitor(this);
        symbolTable = new SymbolTable(null, SymbolTable.ScopeType.Package, "<unusedscope>");
        typeVisitor.pushScope(symbolTable);
    }

    public void visitPackage(String packageName, ParserRuleContext ctx) {
        this.packageName = packageName;
        declOnly = true;
        visit(ctx);
        declOnly = false;
        visit(ctx);
    }

    private void importPackage(String pkgname) {
        SymbolTable importScope = symbolTable.parent;
        SymbolTable pkgscope = packages.get(pkgname);
        if (!declOnly)
            return;
        if (pkgscope == null) {
            logger.severe(String.format("Failed to import package %s", pkgname));
            return;
        }
        logger.info(String.format("Importing package %s", pkgname));
        for (Map.Entry<String,SymbolTableEntry> iterator: pkgscope.bindings.entrySet()) {
            String identifier = iterator.getKey();
            SymbolTableEntry entry = iterator.getValue();
            logger.fine(String.format("Importing %s::%s entry %s", pkgname, identifier, entry));
            SymbolTableEntry oldEntry = importScope.lookup(identifier);
            if (oldEntry != null) {
                logger.info(String.format("Overriding %s::%s", oldEntry.pkgName, identifier));
                importScope.unbind(identifier);
            }
            importScope.bind(identifier, entry);
        }
        for (Map.Entry<String,SymbolTableEntry> iterator: pkgscope.typeBindings.entrySet()) {
            logger.fine(String.format("Importing type %s::%s entry %s", pkgname, iterator.getKey(), iterator.getValue()));
            importScope.bindType(iterator.getKey(), iterator.getValue());
        }
    }

    private void pushScope(ParserRuleContext ctx, SymbolTable.ScopeType st, String name) {
        if (scopes.containsKey(ctx)) {
            symbolTable = scopes.get(ctx);
        } else {
            symbolTable = new SymbolTable(symbolTable, st, name);
            scopes.put(ctx, symbolTable);
        }
        ctxStack.push(ctx);
        logger.fine("pushScope { " + name + "-" + symbolTable + " " + ctx + " " + st
                     + " at " + sourceLocation(ctx));
        typeVisitor.pushScope(symbolTable);
    }

    SymbolTable pushScope(ParserRuleContext ctx) {
        assert scopes.containsKey(ctx) : String.format("Expected to find scope for %s at %s",
                                                       ctx.getText(), sourceLocation(ctx));
        symbolTable = scopes.get(ctx);
        ctxStack.push(ctx);
        logger.fine("pushScope { " + symbolTable.name + "-" + symbolTable + " " + symbolTable.scopeType
                    + " at " + sourceLocation(ctx));
        typeVisitor.pushScope(symbolTable);
        return symbolTable;
    }

    SymbolTable popScope() {
        assert symbolTable.parent != null : String.format("Symbol table %s:%s has no parent", symbolTable.name, symbolTable);
        logger.fine(String.format("popScope -1- %s-%s parent %s-%s at %s }",
                                   symbolTable.name, symbolTable, symbolTable.parent.name, symbolTable.parent,
                                   sourceLocation(ctxStack.peek())));
        assert typeVisitor != null;
        ctxStack.pop();
        typeVisitor.popScope();
        symbolTable = symbolTable.parent;
        return symbolTable;
    }

    static String sourceLocation(ParserRuleContext ctx) {
        Token start = ctx.start;
        TokenSource source = start.getTokenSource();
        return String.format("%s:%d", source.getSourceName(), start.getLine());
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
        if (declOnly) {
            symbolTable = new SymbolTable(null, SymbolTable.ScopeType.Package, packageName + "-imports");
        }
        pushScope(ctx, SymbolTable.ScopeType.Package, packageName);
        if (declOnly)
            importPackage("Prelude");
        packages.put(packageName, symbolTable);
        for (BSVParser.PackagestmtContext stmt : ctx.packagestmt()) {
            visit(stmt);
        }
        popScope();
        return null;
    }

    @Override public Void visitImportdecl(BSVParser.ImportdeclContext importdecl) {
        for (BSVParser.ImportitemContext importitem: importdecl.importitem()) {
            String importedPkgName = importitem.pkgname.getText();
            if (declOnly)
                importPackage(importedPkgName);
        }
        return null;
    }

    @Override
    public Void visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {

        if (!declOnly)
            return null;

        String interfaceName = ctx.typedeftype().typeide().getText();
        logger.fine("entering interface decl " + interfaceName + " {");
        pushScope(ctx, SymbolTable.ScopeType.Declaration, interfaceName);
        BSVType interfaceType = typeVisitor.visit(ctx.typedeftype());
        SymbolTable interfaceMappings = symbolTable;

        visitChildren(ctx);

        popScope();
        for (Map.Entry<String,SymbolTableEntry> mapping: interfaceMappings.bindings.entrySet()) {
            logger.fine(String.format("interface mapping  %s  %s : %s", interfaceName, mapping.getKey(), mapping.getValue().type));
        }
        for (Map.Entry<String,SymbolTableEntry> mapping: interfaceMappings.typeBindings.entrySet()) {
            logger.fine(String.format("interface tmapping %s  %s : %s", interfaceName, mapping.getKey(), mapping.getValue().type));
        }
        symbolTable.bindType(packageName, interfaceName, interfaceType, interfaceMappings);
	SymbolTableEntry interfaceEntry = symbolTable.lookupType(interfaceName);

        for (Map.Entry<String,SymbolTableEntry> mapping: interfaceMappings.bindings.entrySet()) {
	    mapping.getValue().parent = interfaceEntry;
        }
        for (Map.Entry<String,SymbolTableEntry> mapping: interfaceMappings.typeBindings.entrySet()) {
	    mapping.getValue().parent = interfaceEntry;
        }

        logger.fine("} exiting interface decl " + interfaceName);
        return null;
    }

    @Override public Void visitSubinterfacedecl(BSVParser.SubinterfacedeclContext ctx) {
        String subinterfaceName = ctx.lowerCaseIdentifier().getText();
        logger.fine("entering subinterface decl " + subinterfaceName + " {");

        BSVType subinterfaceType = typeVisitor.visit(ctx.bsvtype());

        symbolTable.bind(subinterfaceName, subinterfaceType);

        logger.fine("} exiting sub interface decl " + subinterfaceName);
        return null;
    }

    @Override public Void visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        if (!declOnly)
            return null;
        String typedefname = ctx.upperCaseIdentifier().getText();
        BSVType enumtype = new BSVType(typedefname);
        symbolTable.bind(packageName, typedefname,
                         new SymbolTableEntry(typedefname,
                                              enumtype));
        long tagValue = 0;
        for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String basetagname = elt.upperCaseIdentifier().getText();
            long tagCount = 1;
            boolean numbered = false;
            long tagFrom = 0;

            if (elt.tagval != null) {
		IntValue intValue = new IntValue(elt.tagval.getText());
                tagValue = intValue.value;
            }

            if (elt.from != null) {
                numbered = true;
		IntValue intValue = new IntValue(elt.from.getText());
                tagCount = intValue.value;
                if (elt.to != null) {
                    tagFrom = tagCount;
		    intValue = new IntValue(elt.to.getText());
                    tagCount = intValue.value - tagFrom + 1;
                }
            }

            for (int i = 0; i < tagCount; i++) {
                String tagname = basetagname;
                if (numbered) {
                    tagname = String.format("%s%d", basetagname, tagFrom + i);
                }
                SymbolTableEntry entry = symbolTable.lookup(tagname);
                if (entry != null)
                    logger.fine(String.format("Previously defined entry %s type %s",
                                              tagname, entry.symbolType));
                if (entry == null) {
                    entry = new SymbolTableEntry(tagname, enumtype);
                    symbolTable.bind(packageName, tagname, entry);
                } else {
                    entry.type = new BSVType();
                }
                if (entry.instances == null)
                    entry.instances = new ArrayList<>();
                entry.value = new IntValue(tagValue);
                entry.instances.add(new SymbolTableEntry(tagname, enumtype));
                logger.fine(String.format("Enum tag %s : %s", tagname, enumtype));

                tagValue = tagValue + i;
            }
        }
        return null;
    }

    @Override public Void visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        if (!declOnly)
            return null;
        String typedefname = ctx.typedeftype().getText();
        typeVisitor.visit(ctx);
        return null;
    }

    @Override public Void visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        if (!declOnly)
            return null;
        String typedefname = ctx.typedeftype().typeide().getText();
        BSVType taggeduniontype = typeVisitor.visit(ctx.typedeftype());
	SymbolTable mappings = new SymbolTable(null, SymbolTable.ScopeType.TaggedUnion, typedefname);
        symbolTable.bindType(packageName, typedefname, taggeduniontype, mappings);
        logger.fine(String.format("tagged union %s : %s", typedefname, taggeduniontype));
	int tagnum = 0;
        for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
            BSVParser.UpperCaseIdentifierContext id = member.upperCaseIdentifier();
            String idname = id.getText();
            SymbolTableEntry entry = symbolTable.lookup(idname);
            if (entry != null)
                logger.fine(String.format("Previously defined entry %s type %s",
                                          idname, entry.symbolType));
            if (entry == null) {
                entry = new SymbolTableEntry(idname, taggeduniontype);
                entry.value = new IntValue(tagnum);
                symbolTable.bind(packageName, idname, entry);
            } else {
                entry.type = new BSVType();
            }
            if (entry.instances == null)
                entry.instances = new ArrayList<>();
            entry.instances.add(new SymbolTableEntry(idname, taggeduniontype));

	    logger.fine(String.format("tagged union member %s : %s", idname, taggeduniontype));

	    assert member.subunion() == null : String.format("subunions unhandled %s", ctx.getText());
            if (member.bsvtype() != null) {
		SymbolTableEntry fieldEntry = new SymbolTableEntry(idname, typeVisitor.visit(member.bsvtype()));
		fieldEntry.value = new IntValue(tagnum);
		mappings.bind(idname, fieldEntry);
            } else if (member.substruct() != null) {
		for (BSVParser.StructmemberContext structmember: member.substruct().structmember()) {
		    assert structmember.subunion() == null;
		    String name = String.format("%s$%s", idname, structmember.lowerCaseIdentifier().getText());
		    SymbolTableEntry memberEntry = new SymbolTableEntry(name,
									typeVisitor.visit(structmember.bsvtype()));
		    mappings.bind(name, memberEntry);
		}
            }
            tagnum += 1;
        }
        return null;
    }

    @Override public Void visitTypeclassdecl(BSVParser.TypeclassdeclContext ctx) {
        if (!declOnly)
            return null;
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
            int depth = ctxStack.size();
            if (!declOnly)
                return null;
            pushScope(ctx, SymbolTable.ScopeType.TypeClassInstance, ctx.typeclasside(0).getText());
            if (ctx.provisos() != null)
                visit(ctx.provisos());
            if (functiondef != null)
                visit(functiondef);
            if (moduledef != null)
                visit(moduledef);
            if (varassign != null)
                visit(varassign);

            if (declOnly)
                for (Map.Entry<String,SymbolTableEntry> ste: symbolTable.bindings.entrySet()) {
                    String instanceName = ste.getKey();
                    SymbolTableEntry instanceEntry = ste.getValue();
                    SymbolTableEntry classEntry = symbolTable.lookup(instanceName);
                    assert classEntry != null : String.format("Instance var %s", instanceName);
                    logger.fine(String.format("Adding instance %s : %s", instanceName, instanceEntry.type));
                    classEntry.addInstance(instanceEntry);
                }
            popScope();
            assert depth == ctxStack.size() : "scope stack push/pop mismatch";
        }

        return null;
    }

    @Override
    public Void visitTypedefsynonym(BSVParser.TypedefsynonymContext ctx) {
        if (!declOnly)
            return null;
        String typedefname = ctx.typedeftype().typeide().getText();
        BSVType bsvtype;
        if (ctx.bsvtype() != null)
            bsvtype = typeVisitor.visit(ctx.bsvtype());
        else
            bsvtype = typeVisitor.visit(ctx.functionproto());
        symbolTable.bindType(packageName, typedefname, bsvtype);
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        String modulename = ctx.moduleproto().name.getText();
        BSVType moduletype = typeVisitor.visit(ctx.moduleproto());
        logger.fine(String.format("Binding module %s", modulename));
        if (declOnly) {
            symbolTable.bind(packageName, modulename,
                             new SymbolTableEntry(modulename, moduletype));
            return null;
        }

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
        logger.fine(String.format("Binding import BVI module %s", modulename));
        if (declOnly)
            symbolTable.bind(packageName, modulename,
                             new SymbolTableEntry(modulename, moduletype));
        return null;
    }

    @Override public Void visitMethoddef(BSVParser.MethoddefContext ctx) {
        assert ctx.name != null : String.format("Method with no name %s at %s",
                                                ctx.getText(), sourceLocation(ctx));
        String methodName = ctx.name.getText();
        logger.fine("entering methoddef " + methodName + " {");
        BSVType methodType = new BSVType(); // FIXME
        if (declOnly) {
            symbolTable.bind(methodName, new SymbolTableEntry(methodName, methodType));
            return null;
        }
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
        logger.fine("} exiting methoddef " + methodName);
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
        assert !declOnly;
        String ruleName = (ruledef.name != null) ? ruledef.name.getText() : "<anonrule>";
        logger.fine("entering rule " + ruleName + " {");
        pushScope(ruledef, SymbolTable.ScopeType.Action, ruleName);
        visitChildren(ruledef);
        popScope();
        logger.fine("} exited rule " + ruleName);
        return null;
    }
    @Override public Void visitStmt(BSVParser.StmtContext ctx) {
        return visitChildren(ctx);
    }
    @Override public Void visitMethodproto(BSVParser.MethodprotoContext ctx) {
        String methodname = ctx.name.getText();
        pushScope(ctx, SymbolTable.ScopeType.Declaration, methodname);
        BSVType methodtype = typeVisitor.visit(ctx);
        popScope();
        if (declOnly)
            symbolTable.bind(methodname, new SymbolTableEntry(methodname, methodtype));
        return null;
    }
 
    @Override public Void visitModuleproto(BSVParser.ModuleprotoContext moduleproto) {
        String modulename = unescape(moduleproto.name.getText());
        BSVType moduletype = typeVisitor.visit(moduleproto);
        if (symbolTable.scopeType == SymbolTable.ScopeType.Package) {
            if (declOnly)
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
            if (declOnly)
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
        String functionname = functionproto.name.getText();
        logger.fine("visit functiondef " + functionname);
        visit(functionproto);
        if (declOnly) {
            return null;
        }
        logger.fine(String.format("entering functiondef %s %s {", functionname, declOnly));
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
        logger.fine("} exiting functiondef " + functionname);
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
            logger.fine(String.format("binding methodproto formal %s : %s", varname, bsvtype));
            symbolTable.bind(varname, new SymbolTableEntry(varname, bsvtype));
        }
        return null;
    }
    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
        BSVType bsvtype = typeVisitor.visit(ctx.t);
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
            if (varinit.rhs != null) {
                visit(varinit.rhs);
                BSVType rhstype = new BSVType(); //typeVisitor.visit(varinit.rhs);
                assert rhstype != null : "Null rhstype " + varinit.getText() + " at " + sourceLocation(varinit.rhs);
                logger.fine("varbinding " + rhstype + " " + varinit.getText());
                try {
                    bsvtype.unify(rhstype);
                } catch (InferenceError e) {
                    logger.fine("Var binding InferenceError " + e);
                }
            }
            //logger.fine("VarInit " + typeName + " " + varName);
            if (symbolTable.scopeType == SymbolTable.ScopeType.Package) {
                if (declOnly)
                    symbolTable.bind(packageName, varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
            } else {
                symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
            }
        }
        return null;
    }

    void handleArrowBinding(String varName, BSVType lhsparamtype, BSVType rhstype,
                            ParserRuleContext lhs, ParserRuleContext rhs) {
        assert !declOnly;
        if (varName == null || lhsparamtype == null || rhstype == null) {
            logger.fine(String.format("varName=%s lhsparamtype=%s rhstype=%s\n",
                                             varName, lhsparamtype, rhstype));
            return;
        }

        BSVType lhstype = new BSVType((symbolTable.scopeType == SymbolTable.ScopeType.Module)
                                      ? "Module" : "ActionValue",
                                      lhsparamtype);
        try {
            lhstype.unify(rhstype);
        } catch (InferenceError e) {
            logger.fine("Action binding InferenceError " + e);
        }
        logger.fine("ArrowBinding  " + varName + " : " + lhsparamtype);
        logger.fine("    bsvtype (" + lhstype + ") rhstype (" + rhstype + ")");

    }

    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
        assert !declOnly;
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
        assert !declOnly;
        BSVType rhstype = typeVisitor.visit(ctx.rhs);
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            logger.fine("Let " + varName + " : " + rhstype + " " + ctx.op.getText() + " " + ctx.rhs.getText());
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
        assert !declOnly;
        visit(ctx.lhs);
        visit(ctx.rhs);
        BSVType lhstype = new BSVType(); //typeVisitor.visit(ctx.lhs);
        BSVType rhstype = new BSVType(); //typeVisitor.visit(ctx.rhs);
        BSVType rhsregtype = new BSVType("Reg", rhstype);
        assert lhstype != null : ctx.lhs.getText();
        assert rhstype != null : ctx.rhs.getText();
        if (false) {
            try {
                logger.fine("lhs " + ctx.lhs.getText() + " : " + lhstype.prune());
                logger.fine("rhs " + ctx.rhs.getText() + " : " + rhstype.prune());
                lhstype.unify(rhsregtype);
                logger.fine("regwrite lhs (" + lhstype + ") rhs (" + rhstype + ")");
            } catch (InferenceError e) {
                logger.fine("Reg write InferenceError " + e);
            }
        }
        return null;
    }
    @Override public Void visitIfstmt(BSVParser.IfstmtContext ctx) {
        pushScope(ctx, SymbolTable.ScopeType.IfStmt, "if");
        visit(ctx.expression());
        visit(ctx.stmt(0));
        if (ctx.stmt(1) != null)
            visit(ctx.stmt(1));
        popScope();
        return null;
    }
    @Override public Void visitCasestmt(BSVParser.CasestmtContext ctx) {
        return visitChildren(ctx);
    }
    @Override public Void visitCasestmtitem(BSVParser.CasestmtitemContext ctx)  {
        return visitChildren(ctx);
    }

    @Override public Void visitCasestmtpatitem(BSVParser.CasestmtpatitemContext ctx)  {
        logger.fine("visit case stmt pat item " + ctx.getText());
        pushScope(ctx, SymbolTable.ScopeType.CaseStmt, ctx.pattern().getText());
        visit(ctx.pattern());
        for (BSVParser.ExpressionContext expr: ctx.patterncond().expression())
            visit(expr);
        visit(ctx.stmt());
        popScope();
        return null;
    }

    @Override public Void visitCasestmtdefaultitem(BSVParser.CasestmtdefaultitemContext ctx)  {
        return visitChildren(ctx);
    }
    @Override public Void visitWhilestmt(BSVParser.WhilestmtContext ctx)  {
        assert false : "Unimplemented while stmt" + sourceLocation(ctx);
        return visitChildren(ctx);
    }
    @Override public Void visitForstmt(BSVParser.ForstmtContext ctx)  {
        pushScope(ctx, SymbolTable.ScopeType.Loop, sourceLocation(ctx));
        visit(ctx.forinit());
        visit(ctx.fortest());
        visit(ctx.forincr());
        visit(ctx.stmt());
        popScope();
        return null;
    }
    @Override public Void visitForinit(BSVParser.ForinitContext ctx)  {
        return visitChildren(ctx);
    }
    @Override public Void visitFornewinit(BSVParser.FornewinitContext ctx) {
        BSVType bsvtype = typeVisitor.visit(ctx.bsvtype());
        String varname = ctx.var.getText();
        symbolTable.bind(varname, bsvtype);
        visit(ctx.expression()); //FIXME
        for (BSVParser.SimplevardeclassignContext vardecl: ctx.simplevardeclassign()) {
            if (vardecl.bsvtype() != null)
                bsvtype = typeVisitor.visit(vardecl.bsvtype());
            varname = vardecl.var.getText();
            symbolTable.bind(varname, bsvtype);
            typeVisitor.visit(vardecl.expression());
        }
        return null;
    }
    @Override public Void visitForoldinit(BSVParser.ForoldinitContext ctx) {
        assert false : "Unimplemented for old init " + sourceLocation(ctx);
        return visitChildren(ctx);
    }

    @Override public Void visitSimplevardeclassign(BSVParser.SimplevardeclassignContext ctx) {
        assert false : "Unimplemented simple var decl assign " + sourceLocation(ctx);
        return null;
    }
    @Override public Void visitFortest(BSVParser.FortestContext ctx) {
        return visitChildren(ctx);
    }
    @Override public Void visitForincr(BSVParser.ForincrContext ctx) {
        return visitChildren(ctx);
    }
    @Override public Void visitVarincr(BSVParser.VarincrContext ctx) {
        return visitChildren(ctx);
    }

    @Override public Void visitPattern(BSVParser.PatternContext ctx)  {
        if (ctx.var != null) {
            String varname = ctx.var.getText();
            logger.fine(String.format("binding pattern var %s at %s", varname, sourceLocation(ctx)));
            symbolTable.bind(varname, new BSVType());
        } else {
            logger.fine(String.format("visiting pattern %s", ctx.getText()));
            visitChildren(ctx);
        }
        return null;
    }
    @Override public Void visitConstantpattern(BSVParser.ConstantpatternContext ctx) {
        return null;
    }
    @Override public Void visitTaggedunionpattern(BSVParser.TaggedunionpatternContext ctx)  {
        String tag = ctx.tag.getText();
        if (ctx.pattern() != null)
            visit(ctx.pattern());
        return null;
    }
    @Override public Void visitStructpattern(BSVParser.StructpatternContext ctx)  {
        String tag = ctx.tag.getText();
        for (BSVParser.PatternContext pat: ctx.pattern())
            visit(pat);
        return null;
    }
    @Override public Void visitTuplepattern(BSVParser.TuplepatternContext ctx)  {
        for (BSVParser.PatternContext pat: ctx.pattern())
            visit(pat);
        return visitChildren(ctx);
    }

    @Override public Void visitBeginendblock(BSVParser.BeginendblockContext block) {
        logger.fine("entering block {");
        pushScope(block, symbolTable.scopeType, "begin");

        visitChildren(block);

        popScope();
        logger.fine("} exited block");
        return null;
    }
    @Override public Void visitOperatorexpr(BSVParser.OperatorexprContext ctx) {
        visit(ctx.binopexpr());
        return null;
    }

    @Override public Void visitMatchesexpr(BSVParser.MatchesexprContext ctx) { return visitChildren(ctx); }

    @Override public Void visitCondexpr(BSVParser.CondexprContext ctx) {
        pushScope(ctx, SymbolTable.ScopeType.IfStmt, "condexpr");
        visit(ctx.expression(0));
        visit(ctx.expression(1));
        visit(ctx.expression(2));
        popScope();
        return null;
    }

    @Override public Void visitTripleandexpr(BSVParser.TripleandexprContext ctx) { return visitChildren(ctx); }

    @Override public Void visitCaseexpr(BSVParser.CaseexprContext ctx) {
        assert !declOnly;
        visit(ctx.expression());
        for (BSVParser.CaseexpritemContext item: ctx.caseexpritem()) {
            logger.fine("visit case expr item " + item.getText());
            pushScope(item, SymbolTable.ScopeType.CaseStmt, "caseexpr");
            if (item.pattern() != null)
                visit(item.pattern());
            if (item.patterncond() != null)
                visit(item.patterncond());
            for (BSVParser.ExprprimaryContext expr: item.exprprimary()) {
                visit(expr);
            }
            popScope();
        }
        return null;
    }

    @Override public Void visitReturnexpr(BSVParser.ReturnexprContext ctx) {
        visit(ctx.expression());
        return null;
    }

    @Override public Void visitProvisos(BSVParser.ProvisosContext ctx) {
        return visitChildren(ctx);
    }

    private void bindFreeTypeVars(BSVType t) {
        logger.fine(String.format("bindFreeTypeVars %s %s entry %s", t, t.isVar, symbolTable.lookupType(t.name)));
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

    @Override public Void visitStructexpr(BSVParser.StructexprContext ctx) {
	return null;
    }

    @Override public Void visitProviso(BSVParser.ProvisoContext proviso) {
        logger.fine("visiting proviso " + proviso.getText());
        String varName = proviso.var.getText();
        for (BSVParser.BsvtypeContext t : proviso.bsvtype()) {
            BSVType bsvtype = typeVisitor.visit(t);
            bindFreeTypeVars(bsvtype);
        }
        return null;
    }

    static String getFormalName(BSVParser.MethodprotoformalContext formal) {
	if (formal.name != null) {
	    return formal.name.getText();
	} else {
	    return formal.functionproto().name.getText();
	}
    }

    static BSVType getBsvType(BSVParser.MethodprotoformalContext formal) {
	if (formal.bsvtype() != null) {
	    return getBsvType(formal.bsvtype());
	} else {
	    return getBsvType(formal.functionproto());
	}
    }

    static BSVType getBsvType(BSVParser.BsvtypeContext ctx) {
	if (ctx.functionproto() != null) {
	    return getBsvType(ctx.functionproto());
	} else if (ctx.typenat() != null) {
	    return new BSVType(ctx.typenat().getText(), true);
	} else {
	    String typeide = ctx.typeide().getText();
	    List<BSVType> typeparams = new ArrayList<BSVType>();
	    for (BSVParser.BsvtypeContext param : ctx.bsvtype()) {
		typeparams.add(getBsvType(param));
	    }
	    return new BSVType(typeide, typeparams);
	}
    }

    static BSVType getBsvType(BSVParser.FunctionprotoContext ctx) {
            BSVType returnType =
                (ctx.bsvtype() != null)
                ? getBsvType(ctx.bsvtype())
                : new BSVType("Void");
            List<BSVType> params = new ArrayList<BSVType>();
            if (ctx.methodprotoformals() != null) {
		for (BSVParser.MethodprotoformalContext formal: ctx.methodprotoformals().methodprotoformal()) {
		    params.add(getBsvType(formal));
		}
            }
            int numparams = params.size();
            BSVType functiontype = returnType;
            for (int i = numparams-1; i >= 0; i--) {
                List<BSVType> p = new ArrayList<BSVType>();
                p.add(params.get(i));
                p.add(functiontype);
                functiontype = new BSVType("Function", p);
            }
            logger.fine("functionproto " + ctx.name.getText() + " : " + functiontype);
            return functiontype;
    }

}
