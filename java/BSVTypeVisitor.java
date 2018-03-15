// Generated from BSV.g4 by ANTLR 4.7.1
import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;
import java.util.*;

/**
 * This class provides an empty implementation of {@link BSVVisitor},
 * which can be extended to create a visitor which only needs to handle a subset
 * of the available methods.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public class BSVTypeVisitor extends AbstractParseTreeVisitor<BSVType> implements BSVVisitor<BSVType> {
    private StaticAnalysis staticAnalyzer;
    private SymbolTable scope;
    private Stack<SymbolTable> scopeStack = new Stack<>();

    BSVTypeVisitor(StaticAnalysis staticAnalyzer) {
        this.staticAnalyzer = staticAnalyzer;
    }

    public void pushScope(SymbolTable newScope)
    {
        scopeStack.push(scope);
        scope = newScope;
        System.err.println(String.format("BSVTypeVisitor.pushScope()  %d {", scopeStack.size()));
    }
    public void popScope() {
        System.err.println(String.format("} BSVTypeVisitor.popScope() %d", scopeStack.size()));
        scope = scopeStack.pop();
	assert scopeStack.size() > 0; // nobody should pop the global scope
    }

    BSVType dereferenceTypedef(BSVType bsvtype) {
        assert scope != null;
        assert bsvtype != null;
        SymbolTableEntry entry = scope.lookupType(bsvtype.name);
        if (entry != null) {
            //fixme
            return entry.type;
        }
        return bsvtype;
    }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPackagedef(BSVParser.PackagedefContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPackagedecl(BSVParser.PackagedeclContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitEndpackage(BSVParser.EndpackageContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitLowerCaseIdentifier(BSVParser.LowerCaseIdentifierContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitUpperCaseIdentifier(BSVParser.UpperCaseIdentifierContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitIdentifier(BSVParser.IdentifierContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitAnyidentifier(BSVParser.AnyidentifierContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitExportdecl(BSVParser.ExportdeclContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitExportitem(BSVParser.ExportitemContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitImportdecl(BSVParser.ImportdeclContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitImportitem(BSVParser.ImportitemContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPackagestmt(BSVParser.PackagestmtContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPackageide(BSVParser.PackageideContext ctx) { return visitChildren(ctx); }
        @Override public BSVType visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitInterfacememberdecl(BSVParser.InterfacememberdeclContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodproto(BSVParser.MethodprotoContext ctx) {
            BSVType returnType =
                (ctx.bsvtype() != null)
                ? visit(ctx.bsvtype())
                : (new BSVType("Void"));
            List<BSVType> params = new ArrayList<BSVType>();
            if (ctx.methodprotoformals() != null) {
                BSVType paramType = visit(ctx.methodprotoformals());
                params = paramType.params;
            }
            int numparams = params.size();
            BSVType methodtype = returnType;
            for (int i = numparams-1; i >= 0; i--) {
                List<BSVType> p = new ArrayList<BSVType>();
                p.add(params.get(i));
                p.add(methodtype);
                methodtype = new BSVType("Function", p);
            }
            System.err.println("methodproto " + ctx.name.getText() + " : " + methodtype);
            return methodtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodprotoformals(BSVParser.MethodprotoformalsContext ctx) {
            List<BSVType> params = new ArrayList<BSVType>();
            for (BSVParser.MethodprotoformalContext param : ctx.methodprotoformal())
                params.add(visit(param));
            return new BSVType("MethodProtoFormals", params);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodprotoformal(BSVParser.MethodprotoformalContext ctx) {
            if (ctx.functionproto() != null)
                return visit(ctx.functionproto());
            else if (ctx.bsvtype() != null)
                return visit(ctx.bsvtype());
            else
                return new BSVType("Void");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSubinterfacedecl(BSVParser.SubinterfacedeclContext ctx) {
            assert false;
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedecl(BSVParser.TypedeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedeftype(BSVParser.TypedeftypeContext ctx) {
            BSVType bsvtype = new BSVType(ctx.typeide().getText());
            if (ctx.typeformals() != null) {
                for (BSVParser.TypeformalContext tf: ctx.typeformals().typeformal()) {
                    bsvtype.params.add(visit(tf));
                }
            }
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeformals(BSVParser.TypeformalsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeformal(BSVParser.TypeformalContext ctx) {
            return new BSVType(ctx.typeide().getText());
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedefsynonym(BSVParser.TypedefsynonymContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedefenum(BSVParser.TypedefenumContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedefenumelement(BSVParser.TypedefenumelementContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
            BSVParser.TypedeftypeContext typedeftype = ctx.typedeftype();
            BSVType bsvtype = visit(typedeftype);
            System.err.println(String.format("typedefstruct %s", bsvtype.name));
            SymbolTable fieldMappings = new SymbolTable(scope, SymbolTable.ScopeType.Declaration, bsvtype.name);
            for (BSVParser.StructmemberContext member: ctx.structmember()) {
                assert member.subunion() == null;
                if (member.bsvtype() != null) {
                    BSVType membertype = visit(member.bsvtype());
                    fieldMappings.bind(member.lowerCaseIdentifier().getText(), membertype);
                }
            }
	    System.err.println(String.format("Defining struct %s in scope %s %s",
					     bsvtype.name, scope.name, scope));
            scope.bindType(null, bsvtype.name, bsvtype, fieldMappings);
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
            return visit(ctx.typedeftype());
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitStructmember(BSVParser.StructmemberContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitUnionmember(BSVParser.UnionmemberContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSubstruct(BSVParser.SubstructContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSubunion(BSVParser.SubunionContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitDerives(BSVParser.DerivesContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitVarBinding(BSVParser.VarBindingContext ctx) {
            BSVType bsvtype = visit(ctx.t);
            for (BSVParser.VarinitContext varinit : ctx.varinit()) {
                System.err.println("vardecl " + varinit.var.getText() + " : " + bsvtype);
            }
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitActionBinding(BSVParser.ActionBindingContext ctx) {
            BSVType bsvtype = visit(ctx.t);
            System.err.println("actiondecl " + ctx.var.getText() + " <- " + bsvtype);
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitLetBinding(BSVParser.LetBindingContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPatternBinding(BSVParser.PatternBindingContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitVarinit(BSVParser.VarinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitArraydims(BSVParser.ArraydimsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeclassdecl(BSVParser.TypeclassdeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeclasside(BSVParser.TypeclassideContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedepends(BSVParser.TypedependsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypedepend(BSVParser.TypedependContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypelist(BSVParser.TypelistContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitOverloadeddef(BSVParser.OverloadeddefContext ctx) { return visitChildren(ctx); }
        @Override public BSVType visitOverloadeddecl(BSVParser.OverloadeddeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTctype(BSVParser.TctypeContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModuledef(BSVParser.ModuledefContext ctx) {
            System.err.println("moduledef " + ctx.moduleproto().name.getText());
            return visitChildren(ctx);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModuleproto(BSVParser.ModuleprotoContext ctx) {
            //FIXME: modulecontext
            BSVType moduleInterface =
                (ctx.moduleinterface != null)
                ? visit(ctx.moduleinterface)
                : (new BSVType("Empty"));
            List<BSVType> params = new ArrayList<BSVType>();
            if (ctx.methodprotoformals() != null) {
                BSVType paramType = visit(ctx.methodprotoformals());
                params = paramType.params;
            }
            int numparams = params.size();
            BSVType moduletype = new BSVType("Module");
            moduletype.params.add(moduleInterface);
            for (int i = numparams-1; i >= 0; i--) {
                List<BSVType> p = new ArrayList<BSVType>();
                p.add(params.get(i));
                p.add(moduletype);
                moduletype = new BSVType("Function", p);
            }
            System.err.println("moduleproto " + ctx.name.getText() + " : " + moduletype);
            return moduletype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModulestmt(BSVParser.ModulestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModuleinst(BSVParser.ModuleinstContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModuleapp(BSVParser.ModuleappContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModuleactualparamarg(BSVParser.ModuleactualparamargContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethoddef(BSVParser.MethoddefContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodformals(BSVParser.MethodformalsContext ctx) {
            List<BSVType> params = new ArrayList<BSVType>();
            for (BSVParser.MethodformalContext param : ctx.methodformal())
                params.add(visit(param));
            return new BSVType("MethodFormals", params);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodformal(BSVParser.MethodformalContext ctx) {
            if (ctx.functionproto() != null)
                return visit(ctx.functionproto());
            else if (ctx.bsvtype() != null)
                return visit(ctx.bsvtype());
            else
                return new BSVType("Void");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodcond(BSVParser.MethodcondContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSubinterfacedef(BSVParser.SubinterfacedefContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRuledef(BSVParser.RuledefContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRulecond(BSVParser.RulecondContext ctx) { return visitChildren(ctx); }
        @Override public BSVType visitRulebody(BSVParser.RulebodyContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitFunctiondef(BSVParser.FunctiondefContext ctx) {
            return visitChildren(ctx);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitFunctionproto(BSVParser.FunctionprotoContext ctx) {
            BSVType returnType =
                (ctx.bsvtype() != null)
                ? visit(ctx.bsvtype())
                : new BSVType("Void");
            List<BSVType> params = new ArrayList<BSVType>();
            if (ctx.methodprotoformals() != null) {
                BSVType paramType = visit(ctx.methodprotoformals());
                params = paramType.params;
            }
            int numparams = params.size();
            BSVType functiontype = returnType;
            for (int i = numparams-1; i >= 0; i--) {
                List<BSVType> p = new ArrayList<BSVType>();
                p.add(params.get(i));
                p.add(functiontype);
                functiontype = new BSVType("Function", p);
            }
            System.err.println("functionproto " + ctx.name.getText() + " : " + functiontype);
            return functiontype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitExterncimport(BSVParser.ExterncimportContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitExterncfuncargs(BSVParser.ExterncfuncargsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitExterncfuncarg(BSVParser.ExterncfuncargContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitVarassign(BSVParser.VarassignContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitLvalue(BSVParser.LvalueContext ctx) {
            BSVParser.LvalueContext lvalue = ctx.lvalue();
            if (lvalue != null) {
                System.err.println("computing type of lvalue " + lvalue.getText());
                BSVType lvaluetype = visit(lvalue);
                if (ctx.lowerCaseIdentifier() != null) {
                    String interfaceName = lvaluetype.name;
                    String subname = ctx.lowerCaseIdentifier().getText();
                    SymbolTableEntry entry = scope.lookupType(interfaceName);
                    System.err.println("lvalue field " + interfaceName + "." + subname + "    " + lvaluetype);
                    if (entry != null) {
                        SymbolTableEntry subentry = entry.mappings.lookup(subname);
                        if (subentry != null) {
                            // FIXME: instantiate
                            System.err.println("Subscript " + interfaceName + "." + subname + " : " + subentry.type);
                            return subentry.type;
                        }
                    }
                } else if (ctx.index != null) {
                    // selection of bit or array
                    assert !lvaluetype.isVar : lvalue.getText();
                    if (lvaluetype.name.equals("Vector")) {
                        return lvaluetype.params.get(1);
                    } else {
                        return new BSVType("Bit", new BSVType("1"));
                    }
                } else if (ctx.msb != null && ctx.lsb != null) {
                    assert !lvaluetype.isVar : lvalue.getText();
                    assert false : "Unimplemented: " + lvalue.getText();
                }
            } else if (ctx.lowerCaseIdentifier() != null) {
                SymbolTableEntry entry = scope.lookup(ctx.lowerCaseIdentifier().getText());
                if (entry == null)
                    return new BSVType();
                return entry.type;
            }
            assert false : "Unexpected: " + ctx.getText();
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBsvtype(BSVParser.BsvtypeContext ctx) {
            if (ctx.functionproto() != null) {
                return visit(ctx.functionproto());
            } else if (ctx.typenat() != null) {
                return new BSVType(ctx.typenat().getText(), true);
            } else {
                String typeide = ctx.typeide().getText();
                // is type variable?
                if (typeide.matches("[a-z].*")) {
                    assert typeide != null;
                    assert scope != null : "must have called popScope() too many times";
                    SymbolTableEntry entry = scope.lookupType(typeide);
                    BSVType bsvtype;
                    if (entry == null) {
                        bsvtype = new BSVType(typeide);
                        scope.bindType(typeide, bsvtype);
                    } else {
                        bsvtype = entry.type;
                    }
                    return bsvtype;
                } else {
                    List<BSVType> typeparams = new ArrayList<BSVType>();
                    for (BSVParser.BsvtypeContext param : ctx.bsvtype()) {
                        typeparams.add(visit(param));
                    }
                    return new BSVType(ctx.typeide().getText(), typeparams);
                }
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeide(BSVParser.TypeideContext ctx) {
            if (ctx.var != null) {
                String typeide = ctx.var.getText();
                SymbolTableEntry entry = scope.lookupType(typeide);
                BSVType bsvtype;
                if (entry == null) {
                    bsvtype = new BSVType(typeide);
                    scope.bindType(typeide, bsvtype);
                } else {
                    bsvtype = entry.type;
                }
                return bsvtype;
            } else {
                String typeide = ctx.getText(); //FIXME
                return new BSVType(typeide);
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypenat(BSVParser.TypenatContext ctx) {
            return new BSVType(ctx.getText(), true);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitOperatorexpr(BSVParser.OperatorexprContext ctx) {
            return visit(ctx.binopexpr());
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMatchesexpr(BSVParser.MatchesexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCaseexpr(BSVParser.CaseexprContext ctx) {
            visit(ctx.expression());
            BSVType returnType = new BSVType();
            try {
                for (BSVParser.CaseexpritemContext item: ctx.caseexpritem()) {
                    BSVType itemtype = visit(item);
                    returnType.unify(itemtype);
                }
            } catch (InferenceError e) {
                System.err.println(e);
            }
            return returnType;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCondexpr(BSVParser.CondexprContext ctx) {
            BSVType boolType = new BSVType("Bool");
            BSVType resultType = new BSVType();
            try {
                boolType.unify(visit(ctx.expression(0)));
                resultType.unify(visit(ctx.expression(1)));
                resultType.unify(visit(ctx.expression(2)));
            } catch (InferenceError e) {
                System.err.println(e);
            }
            return resultType;
        }

    @Override public BSVType visitTripleandexpr(BSVParser.TripleandexprContext ctx) { return visitChildren(ctx); }
    @Override public BSVType visitCaseexpritem(BSVParser.CaseexpritemContext ctx) {
        int numExpressions = ctx.exprprimary().size();
        if (ctx.pattern() != null)
            visit(ctx.pattern());
        BSVType matchType = new BSVType();
        for (BSVParser.ExprprimaryContext matchExpr : ctx.exprprimary())
            matchType = visit(matchExpr);
        BSVType boolType = new BSVType("Bool");
        if (ctx.patterncond() != null) {
            for (BSVParser.ExpressionContext condExpr : ctx.patterncond().expression()) {
                BSVType condType = visit(condExpr);
                // boolType.unify(condType);
            }
        }
        BSVType bodyType = visit(ctx.body);
        return bodyType;
    }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPatterncond(BSVParser.PatterncondContext ctx) { return visitChildren(ctx); }
        @Override public BSVType visitBinopexpr(BSVParser.BinopexprContext ctx) {
            if (ctx.unopexpr() != null) {
                return visit(ctx.unopexpr());
            } else {
                BSVType lhstype = visit(ctx.left);
                BSVType rhstype = visit(ctx.right);
                String op = ctx.op.getText();
                assert lhstype != null : String.format("Binopexpr lhstype is null for expr %s at %s",
                                                       ctx.left.getText(), StaticAnalysis.sourceLocation(ctx.left));
                assert rhstype != null : String.format("Binopexpr rhstype is null for expr %s at %s",
                                                       ctx.right.getText(), StaticAnalysis.sourceLocation(ctx.right));
                try {
                    if (lhstype.prune() != rhstype.prune())
                        lhstype.unify(rhstype);
                } catch (InferenceError e) {
                    System.err.println("binop " + op + ": " + e);
                }
                if (op.equals("==") || op.equals("!=")
                    || op.equals("<") || op.equals(">")
                    || op.equals("<=") || op.equals(">=")) {
                    return new BSVType("Bool");
                } else {
                    return lhstype;
                }
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitUnopexpr(BSVParser.UnopexprContext ctx) {
            BSVType bsvtype = visit(ctx.exprprimary());
            if (ctx.op == null) {
                System.err.println("Unop expr " + ctx.exprprimary().getText() + " : " + bsvtype);
                return bsvtype;
            }
            String op = ctx.op.getText();
            if (op.equals("!")) {
                try {
                    bsvtype.unify(new BSVType("Bool"));
                } catch (InferenceError e) {
                    System.err.println(e);
                }
            }
            if (op.equals("&") || op.equals("|") || op.equals("~&") || op.equals("~|")
                || op.equals("^") || op.equals("^~") || op.equals("~^")) {
                try {
                    bsvtype.unify(new BSVType("Bit", new BSVType(null, true)));
                } catch (InferenceError e) {
                    System.err.println(e);
                }
                return new BSVType("Bit", new BSVType(1));
            }
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBitconcat(BSVParser.BitconcatContext ctx) {
            int width = 0;
            boolean widthKnown = true;
            for (BSVParser.ExpressionContext expr: ctx.expression()) {
                BSVType exprtype = visit(expr).prune();
                if (exprtype.isVar) {
                    widthKnown = false;
                    continue;
                }
                exprtype = dereferenceTypedef(exprtype);
                System.err.println(String.format("bitconcat %s type %s", expr.getText(), exprtype));
                if (exprtype.params.size() == 0) {
                    widthKnown = false;
                    continue;
                }

                BSVType widthtype = exprtype.params.get(0).prune();
                if (widthtype.isVar || !widthtype.numeric) {
                    widthKnown = false;
                    continue;
                }
                widthtype = dereferenceTypedef(widthtype);
                System.err.println(String.format("bitconcat %s type %s", expr.getText(), widthtype));
                width += Integer.parseInt(widthtype.name);
            }
            System.err.println(String.format("bitconcat %s width %d known %s at %s",
                                             ctx.getText(), width, widthKnown, StaticAnalysis.sourceLocation(ctx)));
            if (widthKnown)
                return new BSVType("Bit", new BSVType(width));
            else
                return new BSVType("Bit", new BSVType(null, true));
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitVarexpr(BSVParser.VarexprContext ctx) {
            String varName = ctx.anyidentifier().getText();
            if (varName.startsWith("\\"))
                varName = varName.substring(1);
            assert (ctx.pkg == null);
	    assert scope != null : "no scope for " + StaticAnalysis.sourceLocation(ctx);
            SymbolTableEntry entry = scope.lookup(varName);
            System.err.println("var expr " + varName + " entry " + entry);
            System.err.println("var expr " + varName + " entry " + entry + " : " + ((entry != null) ? entry.type : ""));
            assert entry != null : String.format("No symbol table entry for %s at %s", varName, StaticAnalysis.sourceLocation(ctx));
            if (entry.instances != null) {
                for (SymbolTableEntry instance: entry.instances) {
                    System.err.println(String.format("    instance %s : %s", varName, instance.type));
                }
            }
            if (varName.startsWith("$"))
                return new BSVType();
            else
                return entry.type;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBlockexpr(BSVParser.BlockexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitStructexpr(BSVParser.StructexprContext ctx) {
            String structName = ctx.tag.getText();
            SymbolTableEntry entry = scope.lookupType(structName);
            assert entry != null : "No entry for struct " + structName + " in scope " + scope;
            return entry.type;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitStringliteral(BSVParser.StringliteralContext ctx) {
            return new BSVType("String");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRulesexpr(BSVParser.RulesexprContext ctx) {
            return new BSVType("Rule");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitIntliteral(BSVParser.IntliteralContext ctx) {
            String literal = ctx.getText();
            IntValue value = new IntValue(literal);
            if (value.width != 0)
                return new BSVType("Bit", new BSVType(value.width));
            return new BSVType("Integer");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRealliteral(BSVParser.RealliteralContext ctx) {
            return new BSVType("Real");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCastexpr(BSVParser.CastexprContext ctx) { return visit(ctx.bsvtype()); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitResetbyexpr(BSVParser.ResetbyexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitUndefinedexpr(BSVParser.UndefinedexprContext ctx) {
            return new BSVType();
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitClockedbyexpr(BSVParser.ClockedbyexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitReturnexpr(BSVParser.ReturnexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitFieldexpr(BSVParser.FieldexprContext ctx) {
            System.err.println("computing type of field " + ctx.getText());
            BSVType basetype = visit(ctx.exprprimary());
            String interfaceName = basetype.name;
            String subname = ctx.field.getText();
            SymbolTableEntry entry = scope.lookupType(interfaceName);
            System.err.println("expr field " + interfaceName + "." + subname + "    " + basetype);
            if (entry != null)
                System.err.println(" entry.mappings " + entry.mappings);
            if (entry != null && entry.mappings != null) {
                SymbolTableEntry subentry = entry.mappings.lookup(subname);
                System.err.println(String.format(" found %s subname %s subentry %s", entry.name, subname, subentry));
                if (subentry != null) {
                    // FIXME: instantiate interface
                    System.err.println("expr field " + interfaceName + "." + subname + " : " + subentry.type);
                    return subentry.type;
                }
            }
            System.err.println(String.format("Failed to find type of %s at %s", ctx.getText(), StaticAnalysis.sourceLocation(ctx)));
            return new BSVType();
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitParenexpr(BSVParser.ParenexprContext ctx) {
            System.err.println("paren expr " + ctx.getText());
            return visit(ctx.expression());
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitInterfaceexpr(BSVParser.InterfaceexprContext ctx) {
            BSVType bsvtype = visit(ctx.bsvtype());
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitActionblockexpr(BSVParser.ActionblockexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitParfsmexpr(BSVParser.ParfsmexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCallexpr(BSVParser.CallexprContext ctx) {
            System.err.println("call " + ctx.fcn.getText());
            BSVType fcntype = visit(ctx.fcn);
            assert fcntype != null : String.format("Null type for %s at %s", ctx.fcn.getText(), StaticAnalysis.sourceLocation(ctx));
            BSVType resulttype;
            for (BSVParser.ExpressionContext expr: ctx.expression()) {
                resulttype = new BSVType();
                try {
                    BSVType argtype = visit(expr);
                    assert argtype != null : String.format("Null type for %s at %s", expr.getText(), StaticAnalysis.sourceLocation(ctx));
                    BSVType ftype = new BSVType("Function", argtype, resulttype);
                    System.err.println("Apply (" + fcntype + ") to (" + ftype + ")");
                    fcntype.unify(ftype);
                    System.err.println("   -> " + resulttype.prune());
                } catch (InferenceError e) {
                    System.err.println("Apply InferenceError " + e);
                }
                fcntype = resulttype;
            }
            return fcntype.prune();
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitValueofexpr(BSVParser.ValueofexprContext ctx) {
            BSVType bsvtype = visit(ctx.bsvtype());
            return new BSVType("Integer");
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSeqfsmexpr(BSVParser.SeqfsmexprContext ctx) { return visitChildren(ctx); }

        @Override public BSVType visitTaggedunionexpr(BSVParser.TaggedunionexprContext ctx) {
            String tagname = ctx.tag.getText();
            SymbolTableEntry tagentry = scope.lookup(tagname);
            assert tagentry != null : String.format("Failed to lookup tag %s", tagname);
            BSVType tagtype = tagentry.type;
            //FIXME: check type of memberbinds here or in StaticAnalysis
            return tagtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitArraysub(BSVParser.ArraysubContext ctx) {
            BSVType arraytype = visit(ctx.exprprimary());
            assert arraytype != null;
            assert !arraytype.isVar : arraytype;
            if (arraytype.name.equals("Vector"))
                return arraytype.params.get(1);
            else {
                if (ctx.expression().size() == 1)
                    return new BSVType("Bit", new BSVType("1"));
                    assert scope != null;
                // Evaluator eval = new Evaluator(staticAnalyzer, this);
                // try {
                //     IntValue msbValue = (IntValue)eval.evaluate(ctx.expression(0), scope);
                //     IntValue lsbValue = (IntValue)eval.evaluate(ctx.expression(1), scope);
                //     return new BSVType("Bit", new BSVType(msbValue.value - lsbValue.value + 1));
                // } catch (Exception e) {
                //     System.err.println("Failed to evaluate msb or lsb " + e);
                // }
                return new BSVType("Bit", new BSVType());
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitActionvalueblockexpr(BSVParser.ActionvalueblockexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypeassertionexpr(BSVParser.TypeassertionexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMemberbinds(BSVParser.MemberbindsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMemberbind(BSVParser.MemberbindContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitInterfacestmt(BSVParser.InterfacestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRulesstmt(BSVParser.RulesstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBeginendblock(BSVParser.BeginendblockContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitActionblock(BSVParser.ActionblockContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitActionvalueblock(BSVParser.ActionvalueblockContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
    @Override public BSVType visitRegwrite(BSVParser.RegwriteContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitStmt(BSVParser.StmtContext ctx) {
            return visitChildren(ctx);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitIfstmt(BSVParser.IfstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCasestmt(BSVParser.CasestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCasestmtitem(BSVParser.CasestmtitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCasestmtpatitem(BSVParser.CasestmtpatitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCasestmtdefaultitem(BSVParser.CasestmtdefaultitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitWhilestmt(BSVParser.WhilestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitForstmt(BSVParser.ForstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitForinit(BSVParser.ForinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitForoldinit(BSVParser.ForoldinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSimplevarassign(BSVParser.SimplevarassignContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitFornewinit(BSVParser.FornewinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSimplevardeclassign(BSVParser.SimplevardeclassignContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitFortest(BSVParser.FortestContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitForincr(BSVParser.ForincrContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitVarincr(BSVParser.VarincrContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitPattern(BSVParser.PatternContext ctx) {
            if (ctx.var != null) {
                return new BSVType();
            } else {
                return visitChildren(ctx);
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitConstantpattern(BSVParser.ConstantpatternContext ctx) {
            // fixme
            return visitChildren(ctx);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTaggedunionpattern(BSVParser.TaggedunionpatternContext ctx) {
            String tagname = ctx.tag.getText();
            SymbolTableEntry entry = scope.lookup(tagname);
            assert entry != null : String.format("No binding for tagged union tag %s at %s", tagname, StaticAnalysis.sourceLocation(ctx));
            if (ctx.pattern() != null)
                visit(ctx.pattern());
            return entry.type.fresh(new ArrayList<>());
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitStructpattern(BSVParser.StructpatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTuplepattern(BSVParser.TuplepatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitAttributeinstance(BSVParser.AttributeinstanceContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitAttrspec(BSVParser.AttrspecContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitProvisos(BSVParser.ProvisosContext ctx) {
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitProviso(BSVParser.ProvisoContext ctx) {
            return null;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitFsmstmt(BSVParser.FsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitSeqfsmstmt(BSVParser.SeqfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitParfsmstmt(BSVParser.ParfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitIffsmstmt(BSVParser.IffsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitReturnfsmstmt(BSVParser.ReturnfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitWhilefsmstmt(BSVParser.WhilefsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitForfsminit(BSVParser.ForfsminitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitForfsmstmt(BSVParser.ForfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRepeatfsmstmt(BSVParser.RepeatfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitLoopbodyfsmstmt(BSVParser.LoopbodyfsmstmtContext ctx) { return visitChildren(ctx); }
        @Override public BSVType visitPortide(BSVParser.PortideContext ctx) { return visitChildren(ctx); }
        @Override public BSVType visitImportbvi(BSVParser.ImportbviContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBvistmt(BSVParser.BvistmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBviportopt(BSVParser.BviportoptContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBvimethodopt(BSVParser.BvimethodoptContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBvimethodname(BSVParser.BvimethodnameContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBvimethodnames(BSVParser.BvimethodnamesContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBvischedule(BSVParser.BvischeduleContext ctx) { return visitChildren(ctx); }
}
