import java.util.*;
import org.antlr.v4.runtime.ParserRuleContext;

interface Value {
}

interface ArithValue {
    public Value unop(String op);
}

class VoidValue implements Value {
    VoidValue() {}
}

class IntValue implements Value, ArithValue {
    IntValue(int x) {}
    public Value unop(String op) {
	//FIXME
	return this;
    }
}

class FunctionValue implements Value {
    public final String name;
    public final BSVParser.FunctiondefContext function;
    public final BSVParser.ModuledefContext module;
    public final BSVParser.MethoddefContext method;
    public final SymbolTable context;
    public final SymbolTable parentFrame;
    public ArrayList<Value> args;
    public final int argCount;
    public enum FunctionType {
	Function, Module, Action
    };
    public final FunctionType functionType;
    FunctionValue(String name, BSVParser.FunctiondefContext function, SymbolTable context, SymbolTable parentFrame) {
	this.name = name;
	this.function = function;
	this.method = null;
	this.module = null;
	this.context = context;
	this.parentFrame = parentFrame;
	argCount = (function.functionproto().methodprotoformals() == null) ? 0 : function.functionproto().methodprotoformals().methodprotoformal().size();
	this.functionType = FunctionType.Function;
	args = new ArrayList<>();
    }
    FunctionValue(String name, BSVParser.MethoddefContext method, SymbolTable context, SymbolTable parentFrame) {
	this.name = name;
	this.function = null;
	this.method = method;
	this.module = null;
	this.context = context;
	this.parentFrame = parentFrame;
	argCount = (method.methodformals() == null) ? 0 : method.methodformals().methodformal().size();
	this.functionType = FunctionType.Function;
	args = new ArrayList<>();
    }
    FunctionValue(String name, BSVParser.ModuledefContext module, SymbolTable context, SymbolTable parentFrame) {
	this.name = name;
	this.function = null;
	this.method = null;
	this.module = module;
	this.context = context;
	this.parentFrame = parentFrame;
	// implicit argument to delay evaluation until the <- operator
	argCount = 1 + ((module.moduleproto().methodprotoformals() == null)
			? 0
			: module.moduleproto().methodprotoformals().methodprotoformal().size());
	args = new ArrayList<>();
	this.functionType = FunctionType.Module;
    }
    FunctionValue copy() {
	FunctionValue nfv;
	if (function != null)
	    nfv = new FunctionValue(name, function, context, parentFrame);
	if (module != null)
	    nfv = new FunctionValue(name, module, context, parentFrame);
	else
	    nfv = new FunctionValue(name, method, context, parentFrame);
	nfv.args = (ArrayList<Value>)args.clone();
	return nfv;
    }
    int remainingArgCount() {
	return argCount - args.size();
    }
}

class Rule implements Value {
    final public String name;
    final public BSVParser.CondpredicateContext condpredicate;
    final public List<BSVParser.StmtContext> body;
    final public SymbolTable context;

    public Rule(String name, BSVParser.RuledefContext ruledef, SymbolTable context) {
	this.name = name;
	if (ruledef.rulecond() != null)
	    this.condpredicate = ruledef.rulecond().condpredicate();
	else
	    this.condpredicate = null;
	this.body = ruledef.stmt();
	this.context = context;
    }
    public String toString() {
	return "Rule-" + name;
    }
}

class ModuleInstance implements Value {
    final String name;
    final BSVParser.ModuledefContext module;
    final SymbolTable context;
    ModuleInstance(String name, BSVParser.ModuledefContext module, SymbolTable context) {
	this.name = name;
	this.module = module;
	this.context = context;
    }
}
