import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private String pkgname;
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;
    private HashMap<String, SymbolTable> packages;
    private BSVTypeVisitor typeVisitor;

    StaticAnalysis() {
        scopes = new HashMap<ParserRuleContext, SymbolTable>();
        packages = new HashMap<String, SymbolTable>();
        typeVisitor = new BSVTypeVisitor();
        typeVisitor.pushScope(symbolTable);
    }

    public void visitPackage(String pkgname, ParserRuleContext ctx) {
        this.pkgname = pkgname;
        visit(ctx);
    }
    private void pushScope(ParserRuleContext ctx, SymbolTable.ScopeType st) {
        symbolTable = new SymbolTable(symbolTable, st);
        System.err.println("pushScope { " + ctx.getText());
        scopes.put(ctx, symbolTable);
        typeVisitor.pushScope(symbolTable);
    }

    private void popScope() {
        System.err.println("popScope " + symbolTable + " }");
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

    @Override public Void visitPackagedef(BSVParser.PackagedefContext ctx) {
        pushScope(ctx, SymbolTable.ScopeType.Package);
        packages.put(pkgname, symbolTable);
        visitChildren(ctx);
        popScope();
        return null;
    }
    @Override
    public Void visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {
        String interfaceName = ctx.typedeftype().typeide().getText();
        System.err.println("entering interface decl " + interfaceName + " {");
        pushScope(ctx, SymbolTable.ScopeType.Declaration);
        BSVType interfaceType = typeVisitor.visit(ctx.typedeftype());
        SymbolTable interfaceMappings = symbolTable;

        visitChildren(ctx);

        popScope();
        symbolTable.bindType(interfaceName, interfaceType, interfaceMappings);

        System.err.println("} exiting interface decl " + interfaceName);
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

    @Override public Void visitMethoddef(BSVParser.MethoddefContext ctx) {
        String methodName = ctx.name.getText();
        System.err.println("entering methoddef " + methodName + " {");
        BSVType methodType = new BSVType(); // FIXME
        symbolTable.bind(methodName, new SymbolTableEntry(methodName, methodType));
        pushScope(ctx, SymbolTable.ScopeType.Action);
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
        if (ctx.implicitcond() != null)
            visit(ctx.implicitcond());
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
        pushScope(ruledef, SymbolTable.ScopeType.Action);
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
        pushScope(ctx, SymbolTable.ScopeType.Declaration);
        BSVType methodtype = typeVisitor.visit(ctx);
        popScope();
        String methodname = ctx.name.getText();
        symbolTable.bind(methodname, new SymbolTableEntry(methodname, methodtype));
        return null;
    }

    @Override public Void visitFunctiondef(BSVParser.FunctiondefContext ctx) {
        BSVParser.FunctionprotoContext functionproto = ctx.functionproto();
        BSVType functiontype = typeVisitor.visit(functionproto);
        String functionname = functionproto.name.getText();
        System.err.println("entering functiondef " + functionname + " {");
        symbolTable.bind(functionname,
                         new SymbolTableEntry(functionname, functiontype));
        // save the lexical scope
        pushScope(ctx, SymbolTable.ScopeType.Action);
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
            symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
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
            symbolTable.bind(varName, entry);
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
        System.err.println("entering block {");
        pushScope(block, symbolTable.scopeType);

        visitChildren(block);

        popScope();
        System.err.println("} exited block");
        return null;
    }
    @Override public Void visitOperatorExpr(BSVParser.OperatorExprContext ctx) {
        typeVisitor.visit(ctx.binopexpr());
        return null;
    }
}
