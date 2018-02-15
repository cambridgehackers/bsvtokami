// Generated from BSV.g4 by ANTLR 4.7.1
import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;
import org.antlr.v4.runtime.ParserRuleContext;
import java.util.*;


class RuleNotReady extends RuntimeException {
    public RuleNotReady(String message) {
        super(message);
    }
}

/**
 * This class provides an empty implementation of {@link BSVVisitor},
 * which can be extended to create a visitor which only needs to handle a subset
 * of the available methods.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public class Evaluator extends AbstractParseTreeVisitor<Value> implements BSVVisitor<Value> {
    private String modulename;
    private SymbolTable scope;
    private StaticAnalysis staticAnalyzer;
    private BSVTypeVisitor typeVisitor;
    private Stack<SymbolTable> scopeStack;
    private ArrayList<Rule> rules;
    private ArrayList<RegValue> registers;
    private boolean isElaborating = false;
    private boolean finishCalled = false;

    Evaluator(StaticAnalysis staticAnalyzer) {
        this.staticAnalyzer = staticAnalyzer;
        scopeStack = new Stack<>();
        rules = new ArrayList<>();
        registers = new ArrayList<>();
    }

    public Value evaluate(String modulename, ParserRuleContext pkgdef) {
        visit(pkgdef);
        this.modulename = modulename;
        isElaborating = true;
        finishCalled = false;
        pushScope(pkgdef);
        System.err.println("evaluate module " + modulename + " scope " + scope);
        SymbolTableEntry entry = scope.lookup(modulename);
        System.err.println("evaluate module " + modulename + " scope " + scope + " entry " + entry
                           + " constructor "  + ((entry != null) ? entry.value : "<null entry>"));
        if (entry == null) {
            finishCalled = true;
            return new VoidValue();
        }

        FunctionValue constructor = (FunctionValue)entry.value;
        Value instance = instantiateModule(modulename, constructor);
        popScope();
        return instance;
    }

    Value evaluate(ParserRuleContext ctx, SymbolTable newScope) {
        pushScope(newScope);
        Value v = visit(ctx);
        popScope();
        return v;
    }

    boolean isFinished() {
        return finishCalled;
    }

    private void commitRegisters() {
        for (RegValue reg: registers)
            reg.commit();
    }

    private boolean isRuleReady(Rule rule) {
        if (rule.condpredicate == null)
            return true;
        pushScope(rule);
        Value v = visit(rule.condpredicate);
        popScope();
        BoolValue bv = (BoolValue)v;
        if (bv == null) {
            System.err.println("Expecting a BoolValue, got " + v);
            return false;
        }
        return bv.value;
    }

    boolean isMethodReady(FunctionValue mv) {
        BSVParser.MethoddefContext mc = mv.method;
        BSVParser.MethodcondContext methodcond = mc.methodcond();
        if (methodcond == null)
            return true;

        pushScope(mv.context);
        Value v = visit(methodcond.condpredicate());
        popScope();
        BoolValue bv = (BoolValue)v;
        return bv.value;
    }

    public void runRule(Rule rule) {
        pushScope(rule);
        for (BSVParser.StmtContext stmt: rule.body) {
            visit(stmt);
        }
        popScope();
    }

    public int runRulesOnce() {
        isElaborating = false;
        int fire_count = 0;
        for (Rule rule: rules) {
            boolean ready = isRuleReady(rule);
            System.out.println(String.format("Rule %s %s", rule.name, (ready ? "ready" : "")));
            if (ready) {
                try {
                    runRule(rule);
                    commitRegisters();
                    fire_count += 1;
                } catch (RuleNotReady ex) {
                    System.err.println("Rule not ready " + ex);
                }
            }
        }
        return fire_count;
    }

    private void pushScope(ParserRuleContext ctx) {
        SymbolTable newScope = staticAnalyzer.getScope(ctx);
        System.err.println("pushScope {" + ctx.getText());
        pushScope(newScope);
    }
    private void pushScope(Rule rule) {
        SymbolTable newScope = rule.context;
        System.err.println(String.format("pushScope rule %s{", rule.name));
        pushScope(newScope);
    }
    private void pushScope(SymbolTable newScope) {
        scopeStack.push(scope);
        scope = newScope;
    }
    private void popScope() {
        System.err.println("popScope " + " }");
        scope = scopeStack.pop();
    }

    @Override protected Value aggregateResult(Value agg, Value nextResult) {
        //System.err.println("aggregate " + agg + " next " + nextResult);
        if (nextResult == null)
            return agg;
        else
            return nextResult;
    }

        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitPackagedef(BSVParser.PackagedefContext ctx) {
            pushScope(ctx);
            System.err.println("packagedef scope " + scope);
            Value v = visitChildren(ctx);
            popScope();
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitPackagedecl(BSVParser.PackagedeclContext ctx) {
            return visitChildren(ctx);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitEndpackage(BSVParser.EndpackageContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitLowerCaseIdentifier(BSVParser.LowerCaseIdentifierContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitUpperCaseIdentifier(BSVParser.UpperCaseIdentifierContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitIdentifier(BSVParser.IdentifierContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitAnyidentifier(BSVParser.AnyidentifierContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitExportdecl(BSVParser.ExportdeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitExportitem(BSVParser.ExportitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitImportdecl(BSVParser.ImportdeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitImportitem(BSVParser.ImportitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitPackagestmt(BSVParser.PackagestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitInterfacedecl(BSVParser.InterfacedeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitInterfacememberdecl(BSVParser.InterfacememberdeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethodproto(BSVParser.MethodprotoContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethodprotoformals(BSVParser.MethodprotoformalsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethodprotoformal(BSVParser.MethodprotoformalContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSubinterfacedecl(BSVParser.SubinterfacedeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedecl(BSVParser.TypedeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedeftype(BSVParser.TypedeftypeContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeformals(BSVParser.TypeformalsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeformal(BSVParser.TypeformalContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedefsynonym(BSVParser.TypedefsynonymContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedefenum(BSVParser.TypedefenumContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedefenumelement(BSVParser.TypedefenumelementContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedefstruct(BSVParser.TypedefstructContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitStructmember(BSVParser.StructmemberContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitUnionmember(BSVParser.UnionmemberContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSubstruct(BSVParser.SubstructContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSubunion(BSVParser.SubunionContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitDerives(BSVParser.DerivesContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitVarBinding(BSVParser.VarBindingContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitActionBinding(BSVParser.ActionBindingContext ctx) {
            String var = ctx.var.getText();
            SymbolTableEntry entry = scope.lookup(var);
            System.err.println("action bind var " + var + " scope " + scope + " entry " + entry);
            Value v = null;
            if (ctx.rhs != null) {
                v = visit(ctx.rhs);
                System.err.println("  rhs " + ctx.rhs.getText() + " has value " + v);
            }
            if (isElaborating) {
                // module monad
                FunctionValue constructor = (FunctionValue)v;
                v = instantiateModule(constructor.name, constructor);
                entry.setValue(v);
                return v;
            } else {
                // action context
                v = v.read();
                entry.setValue(v);
                return v;
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitLetBinding(BSVParser.LetBindingContext ctx) {
            String var = ctx.lowerCaseIdentifier().get(0).getText();
            SymbolTableEntry entry = scope.lookup(var);
            System.err.println("let var " + var + " scope " + scope + " entry " + entry);
            Value v = null;
            if (ctx.rhs != null) {
                v = visit(ctx.rhs);
                System.err.println("  " + ctx.getText() + " has value " + v);
                entry.setValue(v);
            }
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitPatternBinding(BSVParser.PatternBindingContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitVarinit(BSVParser.VarinitContext ctx) {
            String var = ctx.var.getText();
            SymbolTableEntry entry = scope.lookup(var);
            System.err.println("var " + var + " scope " + scope + " entry " + entry);
            Value v = null;
            if (ctx.rhs != null) {
                v = visit(ctx.rhs);
                System.err.println("  " + ctx.getText() + " has value " + v);
                entry.setValue(v);
            } else {
                // undefined
            }
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitArraydims(BSVParser.ArraydimsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeclassdecl(BSVParser.TypeclassdeclContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeclasside(BSVParser.TypeclassideContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedepends(BSVParser.TypedependsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypedepend(BSVParser.TypedependContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypelist(BSVParser.TypelistContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitOverloadeddef(BSVParser.OverloadeddefContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTctype(BSVParser.TctypeContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModuledef(BSVParser.ModuledefContext ctx) {
            String moduleName = ctx.moduleproto().name.getText();
            SymbolTable moduleScope = staticAnalyzer.getScope(ctx); //.copy(scope);
            FunctionValue constructor = new FunctionValue(moduleName, ctx, moduleScope, scope);
            SymbolTableEntry entry = scope.lookup(moduleName);
            entry.value = constructor;
            return constructor;
        }

    public Value instantiateModule(String instanceName, FunctionValue constructor) {
        System.err.println("Instantiating module " + constructor.name);
        if (constructor.name.equals("mkReg")) {
            RegValue reg = new RegValue(instanceName, constructor.args.get(0));
            registers.add(reg);
            return reg;
        }
        ModuleInstance instance = new ModuleInstance(instanceName,
                                                     constructor.module,
                                                     constructor.context //.copy(constructor.parentFrame)
                                                     );
        pushScope(constructor.module);
        for (BSVParser.ModulestmtContext stmt: constructor.module.modulestmt()) {
            Value v = visit(stmt);
        }
        popScope();
        //BSVParser.ModuledefContext moduledef = constructor.module;
        return instance;
    }

        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModuleproto(BSVParser.ModuleprotoContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModulecontext(BSVParser.ModulecontextContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModulestmt(BSVParser.ModulestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModuleinst(BSVParser.ModuleinstContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModuleapp(BSVParser.ModuleappContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitModuleactualparamarg(BSVParser.ModuleactualparamargContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethoddef(BSVParser.MethoddefContext ctx) {
            SymbolTable methodScope = staticAnalyzer.getScope(ctx);
            String methodName = ctx.name.getText();
            System.err.println("method " + methodName + " scope " + methodScope);
            FunctionValue function = new FunctionValue(methodName, ctx, methodScope, scope);
            scope.lookup(methodName).setValue(function);
            return function;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethodformals(BSVParser.MethodformalsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethodformal(BSVParser.MethodformalContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMethodcond(BSVParser.MethodcondContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSubinterfacedef(BSVParser.SubinterfacedefContext ctx) { return visitChildren(ctx); }

        @Override public Value visitRuledef(BSVParser.RuledefContext ctx) {
            Rule rule = new Rule(ctx.name.getText(), ctx, scope);
            rules.add(rule);
            pushScope(ctx);
            popScope();
            return rule;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitRulecond(BSVParser.RulecondContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitFunctiondef(BSVParser.FunctiondefContext ctx) {
            SymbolTable functionScope = staticAnalyzer.getScope(ctx);
            String functionName = ctx.functionproto().name.getText();
            System.err.println("function " + functionName + " scope " + functionScope);
            FunctionValue function = new FunctionValue(functionName, ctx, functionScope, scope);
            scope.lookup(functionName).setValue(function);
            return function;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitFunctionproto(BSVParser.FunctionprotoContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitExterncimport(BSVParser.ExterncimportContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBigcfuncargs(BSVParser.BigcfuncargsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBigcfuncarg(BSVParser.BigcfuncargContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitVarassign(BSVParser.VarassignContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitLvalue(BSVParser.LvalueContext ctx) {
            if (ctx.lvalue() == null) {
                String varName = ctx.getText();
                SymbolTableEntry entry = scope.lookup(varName);
                return entry.value;
            }
            Value lvalue = visit(ctx.lvalue());
            if (ctx.index != null) {
                return lvalue.sub(visit(ctx.index).read());
            } else if (ctx.lsb != null) {
                return lvalue.sub(visit(ctx.msb).read(), visit(ctx.lsb).read());
            } else if (ctx.lowerCaseIdentifier() != null) {
                System.err.println("Error: Unhandled field access: " + ctx.getText());
                return null;
            }
            return lvalue;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBsvtype(BSVParser.BsvtypeContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeide(BSVParser.TypeideContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypenat(BSVParser.TypenatContext ctx) { return visitChildren(ctx); }
        @Override public Value visitOperatorExpr(BSVParser.OperatorExprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMatchesExpr(BSVParser.MatchesExprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSimpleCondExpr(BSVParser.SimpleCondExprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCaseExpr(BSVParser.CaseExprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCondExpr(BSVParser.CondExprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCaseexpritem(BSVParser.CaseexpritemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCaseexprdefaultitem(BSVParser.CaseexprdefaultitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBinopexpr(BSVParser.BinopexprContext ctx) {
            if (ctx.left == null)
                return visit(ctx.unopexpr());
            System.err.println("visitBinop " + ctx.getText());
            Value left = visit(ctx.left).read();
            Value right = visit(ctx.right).read();
            String op = ctx.op.getText();
            System.err.println(String.format("    %s %s %s", left, op, right));
            return left.binop(op, right);
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitUnopexpr(BSVParser.UnopexprContext ctx) {
            if (ctx.op == null) {
                return visit(ctx.exprprimary());
            } else if (ctx.exprprimary() != null) {
                Value v = visit(ctx.exprprimary());
                return v.unop(ctx.op.getText());
            } else {
                Value v = visit(ctx.unopexpr());
                return v.unop(ctx.op.getText());
            }
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBitconcat(BSVParser.BitconcatContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitVarexpr(BSVParser.VarexprContext ctx) {
            //FIXME package name
            String varName = ctx.anyidentifier().getText();
            SymbolTableEntry entry = scope.lookup(varName);
            System.err.println("var '" + varName + "' entry " + entry + " " + scope + " parent " + scope.parent);
            if (entry != null)
                System.err.println("    entry.value " + entry.value);
            return entry.value;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBlockexpr(BSVParser.BlockexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitStructexpr(BSVParser.StructexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitStringliteral(BSVParser.StringliteralContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitRulesexpr(BSVParser.RulesexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitIntliteral(BSVParser.IntliteralContext ctx) {
            return new IntValue(Integer.parseInt(ctx.IntLiteral().getText()));
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitRealliteral(BSVParser.RealliteralContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCastexpr(BSVParser.CastexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitResetbyexpr(BSVParser.ResetbyexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitUndefinedexpr(BSVParser.UndefinedexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitClockedbyexpr(BSVParser.ClockedbyexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitReturnexpr(BSVParser.ReturnexprContext ctx) {
            Value v = visit(ctx.expression());
            System.err.println("return (" + ctx.expression().getText() + ") = " + v);
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitFieldexpr(BSVParser.FieldexprContext ctx) {
            Value v = visit(ctx.exprprimary());
            String fieldName = ctx.exprfield.getText();
            System.err.println("field expr " + v + " . " + fieldName);
            ModuleInstance instance = (ModuleInstance)v;
            SymbolTableEntry entry = instance.context.lookup(fieldName);
            if (entry != null) {
                System.err.println("  method " + entry.value);
                return entry.value;
            }
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitParenexpr(BSVParser.ParenexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitInterfaceexpr(BSVParser.InterfaceexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitActionblockexpr(BSVParser.ActionblockexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitParfsmstmtexpr(BSVParser.ParfsmstmtexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCallexpr(BSVParser.CallexprContext ctx) {
            FunctionValue closure = (FunctionValue)visit(ctx.fcn);
            System.err.println("closure " + closure);
            ArrayList<Value> argValues = new ArrayList<>();
            for (BSVParser.ExpressionContext argExpr: ctx.expression()) {
                argValues.add(visit(argExpr));
            }
            if (closure.name.equals("$methodready")) {
                FunctionValue mv = (FunctionValue)argValues.get(0);
                return new BoolValue (isMethodReady(mv));
            }
            if (closure.name.equals("$finish")) {
                finishCalled = true;
                return new VoidValue();
            }
            if (argValues.size() < closure.remainingArgCount()) {
                FunctionValue newClosure = closure.copy();
                newClosure.args.addAll(argValues);
                return newClosure;
            }
            ParserRuleContext defcontext = (closure.function != null) ? closure.function : closure.method;
            SymbolTable functionScope = staticAnalyzer.getScope(defcontext);
            System.err.println("calling " + closure.name + " fcn (" + closure.name + ") scope " + scope);
            //functionScope = functionScope.copy(closure.parentFrame);
            pushScope(defcontext);
            if (argValues.size() > 0) {
                List<String> formalVars = (closure.function != null)
                    ? getFormalVars(closure.function)
                    : getFormalVars(closure.method);
                int argnum = 0;
                for (Value argValue: argValues) {
                    String varName = formalVars.get(argnum);
                    SymbolTableEntry entry = scope.lookup(varName);
                    if (entry == null) {
                        System.err.println("Did not find entry for function " + closure.name + " var " + varName);
                    }
                    entry.value = argValue;
                    argnum += 1;
                }
            }
            Value v = new VoidValue();
            if (closure.function != null) {
                if (closure.function.expression() != null) {
                    v = visit(closure.function.expression());
                } else {
                    for (BSVParser.StmtContext stmt: closure.function.stmt()) {
                        v = visit(stmt);
                    }
                }
            } else {
                boolean ready = isMethodReady(closure);
                if (!ready)
                    throw new RuleNotReady(closure.name);
                if (closure.method.expression() != null) {
                    v = visit(closure.method.expression());
                } else {
                    for (BSVParser.StmtContext stmt: closure.method.stmt()) {
                        v = visit(stmt);
                    }
                }
            }
            popScope();
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitValueofexpr(BSVParser.ValueofexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSeqfsmstmtexpr(BSVParser.SeqfsmstmtexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTaggedunionexpr(BSVParser.TaggedunionexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitArraysub(BSVParser.ArraysubContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitActionvalueblockexpr(BSVParser.ActionvalueblockexprContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTypeassertion(BSVParser.TypeassertionContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMemberbinds(BSVParser.MemberbindsContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitMemberbind(BSVParser.MemberbindContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitInterfacestmt(BSVParser.InterfacestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitRulesstmt(BSVParser.RulesstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBeginendblock(BSVParser.BeginendblockContext block) {
            pushScope(block);

            System.err.println("entering block scope " + scope + " {");
            Value v = null;
            for (BSVParser.StmtContext stmt: block.stmt()) {
                v = visit(stmt);
            }
            System.err.println("} exited block");

            popScope();
            return v;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitActionblock(BSVParser.ActionblockContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitActionvalueblock(BSVParser.ActionvalueblockContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitRegwrite(BSVParser.RegwriteContext ctx) {
            Value lhs = visit(ctx.lhs);
            Value rhs = visit(ctx.rhs).read();
            RegValue reg = (RegValue)lhs;
            System.out.println(String.format("Updating reg %s/%s with value %s", ctx.lhs.getText(), reg, rhs));
            reg.update(rhs);
            return rhs;
        }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitStmt(BSVParser.StmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitIfstmt(BSVParser.IfstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCasestmt(BSVParser.CasestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCasestmtitem(BSVParser.CasestmtitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCasestmtpatitem(BSVParser.CasestmtpatitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBigdefaultitem(BSVParser.BigdefaultitemContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitWhilestmt(BSVParser.WhilestmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitForstmt(BSVParser.ForstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitForinit(BSVParser.ForinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitForoldinit(BSVParser.ForoldinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSimplevarassign(BSVParser.SimplevarassignContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitFornewinit(BSVParser.FornewinitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSimplevardeclassign(BSVParser.SimplevardeclassignContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitFortest(BSVParser.FortestContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitForincr(BSVParser.ForincrContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitVarincr(BSVParser.VarincrContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitCondpredicate(BSVParser.CondpredicateContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitPattern(BSVParser.PatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitConstantpattern(BSVParser.ConstantpatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTaggedunionpattern(BSVParser.TaggedunionpatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitStructpattern(BSVParser.StructpatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitTuplepattern(BSVParser.TuplepatternContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitAttributeinstance(BSVParser.AttributeinstanceContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitAttrspec(BSVParser.AttrspecContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitProvisos(BSVParser.ProvisosContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitProviso(BSVParser.ProvisoContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitFsmstmt(BSVParser.FsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitSeqfsmstmt(BSVParser.SeqfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitParfsmstmt(BSVParser.ParfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitIffsmstmt(BSVParser.IffsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitReturnfsmstmt(BSVParser.ReturnfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitWhilefsmstmt(BSVParser.WhilefsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitForfsminit(BSVParser.ForfsminitContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitForfsmstmt(BSVParser.ForfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitRepeatfsmstmt(BSVParser.RepeatfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitLoopbodyfsmstmt(BSVParser.LoopbodyfsmstmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitImportbvi(BSVParser.ImportbviContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBvistmt(BSVParser.BvistmtContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBviportopt(BSVParser.BviportoptContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBvimethodopt(BSVParser.BvimethodoptContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBvimethodname(BSVParser.BvimethodnameContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBvimethodnames(BSVParser.BvimethodnamesContext ctx) { return visitChildren(ctx); }
        /**
         * {@inheritDoc}
         *
         * <p>The default implementation returns the result of calling
         * {@link #visitChildren} on {@code ctx}.</p>
         */
        @Override public Value visitBvischedule(BSVParser.BvischeduleContext ctx) { return visitChildren(ctx); }

    List<String> getFormalVars(BSVParser.FunctiondefContext function) {
        ArrayList<String> formalVars = new ArrayList<>();
                BSVParser.MethodprotoformalsContext formals = function.functionproto().methodprotoformals();
                int argnum = 0;

                for (BSVParser.MethodprotoformalContext formal: formals.methodprotoformal()) {
                    String varName;
                    if (formal.name != null)
                        varName = formal.name.getText();
                    else
                        varName = formal.functionproto().name.getText();
                    formalVars.add(varName);
                }
            return formalVars;
    }
    List<String> getFormalVars(BSVParser.MethoddefContext method) {
        ArrayList<String> formalVars = new ArrayList<>();
        BSVParser.MethodformalsContext formals = method.methodformals();
        int argnum = 0;
        for (BSVParser.MethodformalContext formal : formals.methodformal()) {
            String varName;
            if (formal.name != null)
                varName = formal.name.getText();
            else
                varName = formal.functionproto().name.getText();
            formalVars.add(varName);
        }
        return formalVars;
    }
}
