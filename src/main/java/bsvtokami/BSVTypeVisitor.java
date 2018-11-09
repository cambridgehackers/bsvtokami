package bsvtokami;

import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;
import org.antlr.v4.runtime.ParserRuleContext;
import java.util.*;
import java.util.logging.Logger;

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
    private HashMap<ParserRuleContext, BSVType> types;
    private static Logger logger = Logger.getGlobal();
    private static boolean callUnify = false;

    BSVTypeVisitor(StaticAnalysis staticAnalyzer) {
        this.staticAnalyzer = staticAnalyzer;
	types = new HashMap<>();
    }

    public void pushScope(SymbolTable newScope)
    {
	assert newScope != null : "BSVTypeVisitor.pushScope requires non-null scope";
        scopeStack.push(scope);
        scope = newScope;
        //System.err.println(String.format("BSVTypeVisitor.pushScope()  %s {", scope.name));
    }
    public void popScope() {
        //System.err.println(String.format("} BSVTypeVisitor.popScope() %s", scope.name));
        scope = scopeStack.pop();
	assert scopeStack.size() > 0; // nobody should pop the global scope
    }

    BSVType dereferenceTypedef(BSVType bsvtype) {
        assert scope != null;
        assert bsvtype != null;
        SymbolTableEntry entry = scope.lookupType(bsvtype.name);
        if (entry != null) {
	    //fixme
	    if (entry.pkgName != null)
		return entry.type.fresh(new ArrayList<>());
	    else
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
	    SymbolTableEntry entry = scope.lookup(ctx.getText());
	    assert entry != null;
	    assert entry.type != null;
            return entry.type;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
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
            logger.fine("methodproto " + ctx.name.getText() + " : " + methodtype);
	    types.put(ctx, methodtype);
            return methodtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodprotoformals(BSVParser.MethodprotoformalsContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            List<BSVType> params = new ArrayList<BSVType>();
            for (BSVParser.MethodprotoformalContext param : ctx.methodprotoformal())
                params.add(visit(param));
	    BSVType bsvtype = new BSVType("MethodProtoFormals", params);
	    types.put(ctx, bsvtype);
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitMethodprotoformal(BSVParser.MethodprotoformalContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            if (ctx.functionproto() != null)
                return visit(ctx.functionproto());
            else if (ctx.bsvtype() != null)
                return visit(ctx.bsvtype());
            else {
		BSVType bsvtype = new BSVType("Void");
		types.put(ctx, bsvtype);
		return bsvtype;
	    }
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = new BSVType(ctx.typeide().getText());
            if (ctx.typeformals() != null) {
                for (BSVParser.TypeformalContext tf: ctx.typeformals().typeformal()) {
                    bsvtype.params.add(visit(tf));
                }
            }
	    types.put(ctx, bsvtype);
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
            BSVType bsvtype = new BSVType(ctx.typeide().getText(), ctx.numeric != null);
	    types.put(ctx, bsvtype);
	    return bsvtype;
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
            logger.fine(String.format("typedefstruct %s", bsvtype.name));
            SymbolTable fieldMappings = new SymbolTable(scope, SymbolTable.ScopeType.Declaration, bsvtype.name);
            for (BSVParser.StructmemberContext member: ctx.structmember()) {
                assert member.subunion() == null;
                if (member.bsvtype() != null) {
                    BSVType membertype = visit(member.bsvtype());
                    fieldMappings.bind(member.lowerCaseIdentifier().getText(), membertype);
                }
            }
	    logger.fine(String.format("Defining struct %s in scope %s %s",
				      bsvtype.name, scope.name, scope));
            scope.bindType(null, bsvtype.name, bsvtype, fieldMappings)
		.setSymbolType(SymbolType.Struct);
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
		BSVType rhsType = null;
		if (varinit.rhs != null) {
		    rhsType = visit(varinit.rhs);
		}
                System.err.println("vardecl " + varinit.var.getText() + " : " + bsvtype + " rhs type: " + rhsType );
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
            logger.fine("actiondecl " + ctx.var.getText() + " <- " + bsvtype);
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
            logger.fine("moduledef " + ctx.moduleproto().name.getText());
            return visitChildren(ctx);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitModuleproto(BSVParser.ModuleprotoContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
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
            logger.fine("moduleproto " + ctx.name.getText() + " : " + moduletype);
	    types.put(ctx, moduletype);
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            List<BSVType> params = new ArrayList<BSVType>();
            for (BSVParser.MethodformalContext param : ctx.methodformal())
                params.add(visit(param));
            BSVType bsvtype = new BSVType("MethodFormals", params);
	    types.put(ctx, bsvtype);
	    return bsvtype;
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
	    return StaticAnalysis.getBsvType(ctx);
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
                logger.fine("computing type of lvalue " + lvalue.getText());
                BSVType lvaluetype = visit(lvalue);
                if (ctx.lowerCaseIdentifier() != null) {
                    String interfaceName = lvaluetype.name;
                    String subname = ctx.lowerCaseIdentifier().getText();
                    SymbolTableEntry entry = scope.lookupType(interfaceName);
                    logger.fine("lvalue field " + interfaceName + "." + subname + "    " + lvaluetype);
                    if (entry != null) {
                        SymbolTableEntry subentry = entry.mappings.lookup(subname);
                        if (subentry != null) {
                            // FIXME: instantiate
                            logger.fine("Subscript " + interfaceName + "." + subname + " : " + subentry.type);
                            return subentry.type;
                        }
                    }
                } else if (ctx.index != null) {
                    // selection of bit or array
                    assert !lvaluetype.isVar : lvalue.getText();
                    if (lvaluetype.name.equals("Vector")) {
                        return lvaluetype.params.get(1);
                    } else {
			BSVType bsvtype = new BSVType("Bit", new BSVType("1"));
			types.put(ctx, bsvtype);
			return bsvtype;
                    }
                } else if (ctx.msb != null && ctx.lsb != null) {
                    assert !lvaluetype.isVar : lvalue.getText();
                    assert false : "Unimplemented: " + lvalue.getText();
                }
            } else if (ctx.lowerCaseIdentifier() != null) {
                SymbolTableEntry entry = scope.lookup(ctx.lowerCaseIdentifier().getText());
                if (entry == null) {
                    BSVType bsvtype = new BSVType();
		    types.put(ctx, bsvtype);
		}
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
                BSVType bsvtype = new BSVType(ctx.typenat().getText(), true);
		types.put(ctx, bsvtype);
		return bsvtype;
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
		    types.put(ctx, bsvtype);
                    return bsvtype;
                } else {
                    List<BSVType> typeparams = new ArrayList<BSVType>();
                    for (BSVParser.BsvtypeContext param : ctx.bsvtype()) {
                        typeparams.add(visit(param));
                    }
                    BSVType bsvtype = new BSVType(ctx.typeide().getText(), typeparams);
		    types.put(ctx, bsvtype);
		    return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            if (ctx.var != null) {
                String typeide = ctx.var.getText();
                SymbolTableEntry entry = scope.lookupType(typeide);
                BSVType bsvtype;
                if (entry == null) {
                    bsvtype = new BSVType(typeide);
                    scope.bindType(typeide, bsvtype);
                } else {
		    if (entry.pkgName != null)
			bsvtype = entry.type.fresh(new ArrayList<>());
		    else
			bsvtype = entry.type;
                }
		types.put(ctx, bsvtype);
                return bsvtype;
            } else {
                String typeide = ctx.getText(); //FIXME
		System.err.println("fixme typeide " + ctx.getText());
		BSVType bsvtype = new BSVType(typeide);
		types.put(ctx, bsvtype);
		return bsvtype;
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitTypenat(BSVParser.TypenatContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = new BSVType(ctx.getText(), true);
	    types.put(ctx, bsvtype);
	    return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            visit(ctx.expression());
            BSVType returnType = new BSVType();
            try {
                for (BSVParser.CaseexpritemContext item: ctx.caseexpritem()) {
                    BSVType itemtype = visit(item);
		    if (callUnify)
			returnType.unify(itemtype);
                }
            } catch (InferenceError e) {
                logger.fine(e.toString());
            }
	    types.put(ctx, returnType);
            return returnType;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitCondexpr(BSVParser.CondexprContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType boolType = new BSVType("Bool");
            BSVType resultType = new BSVType();
	    if (callUnify) {
		try {
		    boolType.unify(visit(ctx.expression(0)));
		    resultType.unify(visit(ctx.expression(1)));
		    resultType.unify(visit(ctx.expression(2)));
		} catch (InferenceError e) {
		    logger.fine(e.toString());
		}
	    }
	    types.put(ctx, resultType);
            return resultType;
        }

    @Override public BSVType visitTripleandexpr(BSVParser.TripleandexprContext ctx) { return visitChildren(ctx); }
    @Override public BSVType visitCaseexpritem(BSVParser.CaseexpritemContext ctx) {
	if (types.containsKey(ctx))
	    return types.get(ctx);
        int numExpressions = ctx.exprprimary().size();
        if (ctx.pattern() != null)
            visit(ctx.pattern());
        BSVType matchType = new BSVType();
        for (BSVParser.ExprprimaryContext matchExpr : ctx.exprprimary())
            matchType = visit(matchExpr);
        BSVType boolType = new BSVType("Bool");
        if (ctx.patterncond() != null) {
            for (BSVParser.PatterncondContext patternCond : ctx.patterncond()) {
                BSVType condType = visit(patternCond.expression());
		//if (callUnify)
		//    boolType.unify(condType);
            }
        }
        BSVType bodyType = visit(ctx.body);
	types.put(ctx, bodyType);
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
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
		if (callUnify) {
		    try {
			if (lhstype.prune() != rhstype.prune())
			    lhstype.unify(rhstype);
		    } catch (InferenceError e) {
			logger.fine("binop " + op + ": " + e);
		    }
		}
                if (op.equals("==") || op.equals("!=")
                    || op.equals("<") || op.equals(">")
                    || op.equals("<=") || op.equals(">=")) {
                    BSVType bsvtype = new BSVType("Bool");
		    types.put(ctx, bsvtype);
		    return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = visit(ctx.exprprimary());
            if (ctx.op == null) {
                logger.fine("Unop expr " + ctx.exprprimary().getText() + " : " + bsvtype);
                return bsvtype;
            }
            String op = ctx.op.getText();
            if (op.equals("!")) {
                try {
		    if (callUnify)
			bsvtype.unify(new BSVType("Bool"));
                } catch (InferenceError e) {
                    logger.fine(e.toString());
                }
            }
            if (op.equals("&") || op.equals("|") || op.equals("~&") || op.equals("~|")
                || op.equals("^") || op.equals("^~") || op.equals("~^")) {
                try {
		    if (callUnify)
			bsvtype.unify(new BSVType("Bit", new BSVType(null, true)));
                } catch (InferenceError e) {
                    logger.fine(e.toString());
                }
                return new BSVType("Bit", new BSVType(1));
            }
	    types.put(ctx, bsvtype);
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitBitconcat(BSVParser.BitconcatContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            int width = 0;
            boolean widthKnown = true;
            for (BSVParser.ExpressionContext expr: ctx.expression()) {
                BSVType exprtype = visit(expr).prune();
                if (exprtype.isVar) {
                    widthKnown = false;
                    continue;
                }
                exprtype = dereferenceTypedef(exprtype);
                logger.fine(String.format("bitconcat %s type %s", expr.getText(), exprtype));
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
                logger.fine(String.format("bitconcat %s type %s", expr.getText(), widthtype));
                width += Integer.parseInt(widthtype.name);
            }
            logger.fine(String.format("bitconcat %s width %d known %s at %s",
                                             ctx.getText(), width, widthKnown, StaticAnalysis.sourceLocation(ctx)));
	    BSVType bsvtype = (widthKnown)
		? new BSVType("Bit", new BSVType(width))
		: new BSVType("Bit", new BSVType(null, true));
	    types.put(ctx, bsvtype);
	    return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitVarexpr(BSVParser.VarexprContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            String varName = ctx.anyidentifier().getText();
            if (varName.startsWith("\\"))
                varName = varName.substring(1);
            assert (ctx.pkg == null);
	    assert scope != null : "no scope for " + StaticAnalysis.sourceLocation(ctx);
            SymbolTableEntry entry = scope.lookup(varName);
            assert entry != null || varName.startsWith("$")
		: String.format("No symbol table entry for %s at %s", varName, StaticAnalysis.sourceLocation(ctx));
            logger.fine("var expr " + varName + " entry " + entry + " : " + ((entry != null) ? entry.type : ""));
            if (entry != null && entry.instances != null) {
                for (SymbolTableEntry instance: entry.instances) {
                    logger.fine(String.format("    instance %s : %s", varName, instance.type));
                }
            }
	    BSVType entryType;
            if (varName.startsWith("$"))
                entryType = new BSVType("Function", new BSVType(), new BSVType());
            else {
		entryType = entry.type;
		if (entry.pkgName != null)
		    entryType = entryType.fresh(new ArrayList<>());
	    }
	    types.put(ctx, entryType);
	    return entryType;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            String structName = ctx.tag.getText();
            SymbolTableEntry entry = scope.lookupType(structName);
            assert entry != null : "No entry for struct " + structName + " in scope " + scope;
	    System.err.println(String.format("type struct expr %s mappings %s",
					     structName,
					     entry.mappings.name));
	    SymbolTable mappings = entry.mappings;
	    if (ctx.memberbinds() != null) {
		for (BSVParser.MemberbindContext memberbind: ctx.memberbinds().memberbind()) {
		    String fieldName = memberbind.field.getText();
		    BSVType exprType = visit(memberbind.expression());
		    SymbolTableEntry fieldEntry = mappings.lookup(fieldName);
		    assert fieldEntry != null;
		    try {
			exprType.unify(fieldEntry.type.fresh(new ArrayList<>()));
			System.err.println(String.format("    unify %s type %s expr type %s %s",
							 fieldName, fieldEntry.type,
							 exprType, exprType.prune()));
		    } catch (InferenceError e) {
			logger.fine("Apply InferenceError " + e);
		    }
		}
	    }
	    types.put(ctx, entry.type);
	    return entry.type;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitStringliteral(BSVParser.StringliteralContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = new BSVType("String");
	    types.put(ctx, bsvtype);
	    return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRulesexpr(BSVParser.RulesexprContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = new BSVType("Rule");
	    types.put(ctx, bsvtype);
	    return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitIntliteral(BSVParser.IntliteralContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            String literal = ctx.getText();
            IntValue value = new IntValue(literal);
	    BSVType bsvtype = (value.width != 0)
		? new BSVType("Bit", new BSVType(value.width))
		: new BSVType("Bit", new BSVType(null, true));
	    if (value.width == 0)
		System.err.println("Integer type at " + StaticAnalysis.sourceLocation(ctx));
	    types.put(ctx, bsvtype);
            return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitRealliteral(BSVParser.RealliteralContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = new BSVType("Real");
	    types.put(ctx, bsvtype);
	    return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = new BSVType();
	    types.put(ctx, bsvtype);
	    return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            logger.fine("computing type of field " + ctx.getText());
            BSVType basetype = visit(ctx.exprprimary());
            String interfaceName = basetype.name;
            String subname = ctx.field.getText();
            SymbolTableEntry entry = scope.lookupType(interfaceName);
            logger.fine("expr field " + interfaceName + "." + subname + "    " + basetype);
            if (entry != null)
                logger.fine(" entry.mappings " + entry.mappings);
            if (entry != null && entry.mappings != null) {
                SymbolTableEntry subentry = entry.mappings.lookup(subname);
                logger.fine(String.format(" found %s subname %s subentry %s", entry.name, subname, subentry));
                if (subentry != null) {
                    // FIXME: instantiate interface
                    logger.fine("expr field " + interfaceName + "." + subname + " : " + subentry.type);
                    return subentry.type;
                }
            }
            logger.fine(String.format("Failed to find type of %s at %s", ctx.getText(), StaticAnalysis.sourceLocation(ctx)));
            BSVType bsvtype = new BSVType();
	    types.put(ctx, bsvtype);
	    return bsvtype;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitParenexpr(BSVParser.ParenexprContext ctx) {
            logger.fine("paren expr " + ctx.getText());
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType fcntype = visit(ctx.fcn).fresh(new ArrayList<>());
            System.err.println("call " + ctx.fcn.getText() + " type " + fcntype + " at " + StaticAnalysis.sourceLocation(ctx));
            assert fcntype != null : String.format("Null type for %s at %s", ctx.fcn.getText(), StaticAnalysis.sourceLocation(ctx));
            BSVType resulttype = new BSVType();
	    BSVType fcntype_i = fcntype;
	    int i = 0;
            for (BSVParser.ExpressionContext expr: ctx.expression()) {
                resulttype = new BSVType();
                try {
                    BSVType argtype = visit(expr);
                    assert argtype != null : String.format("Null type for %s at %s", expr.getText(), StaticAnalysis.sourceLocation(ctx));
                    BSVType ftype = new BSVType("Function", argtype, resulttype);
                    System.err.println("    " + i + " Apply (" + fcntype_i + ") to (" + ftype + ")");
		    if (true || callUnify)
			fcntype_i.unify(ftype);
                    System.err.println("    " + i + " Apply (" + fcntype_i + ") to (" + ftype + ")"
				       + " result type " + resulttype.prune());
                    logger.fine("   -> " + resulttype.prune());
                } catch (InferenceError e) {
                    logger.fine("Apply InferenceError " + e);
                }
                fcntype_i = resulttype;
		i++;
            }
	    BSVType bsvtype = fcntype.prune();
	    System.err.println("    now type " + bsvtype + " resulttype " + resulttype);
	    types.put(ctx, resulttype.prune());
	    return resulttype.prune();
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public BSVType visitValueofexpr(BSVParser.ValueofexprContext ctx) {
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType bsvtype = visit(ctx.bsvtype());
	    bsvtype = new BSVType("Integer");
	    types.put(ctx, bsvtype);
	    return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            BSVType arraytype = visit(ctx.exprprimary());
            assert arraytype != null;
            assert !arraytype.isVar : String.format("Array type is variable at %s",
						    StaticAnalysis.sourceLocation(ctx));
            if (arraytype.name.equals("Vector"))
                return arraytype.params.get(1);
            else {
                if (ctx.expression().size() == 1) {
                    BSVType bsvtype = new BSVType("Bit", new BSVType("1"));
		    types.put(ctx, bsvtype);
		    return bsvtype;
		}
		    
		assert scope != null;
                // Evaluator eval = new Evaluator(staticAnalyzer, this);
                // try {
                //     IntValue msbValue = (IntValue)eval.evaluate(ctx.expression(0), scope);
                //     IntValue lsbValue = (IntValue)eval.evaluate(ctx.expression(1), scope);
                //     return new BSVType("Bit", new BSVType(msbValue.value - lsbValue.value + 1));
                // } catch (Exception e) {
                //     logger.fine("Failed to evaluate msb or lsb " + e);
                // }
                BSVType bsvtype = new BSVType("Bit", new BSVType());
		types.put(ctx, bsvtype);
		return bsvtype;
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
	    if (types.containsKey(ctx))
		return types.get(ctx);
            if (ctx.var != null) {
                BSVType bsvtype = new BSVType();
		types.put(ctx, bsvtype);
		return bsvtype;
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
