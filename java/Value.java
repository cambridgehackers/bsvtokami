import java.util.*;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.antlr.v4.runtime.ParserRuleContext;

class Value {
    Value read() {
        return this;
    }
    public Value cast(BSVType bsvtype) { return this; }
    public Value unop(String op) { return this; }
    public Value binop(String op, Value other) { return this; }
    public Value sub(Value index) { return this; }
    public Value sub(Value msb, Value lsb) { return this; }
}

class VoidValue extends Value {
    VoidValue() {}
}

class IntValue extends Value {
    private static Logger logger = Logger.getGlobal();
    final long value;
    final int width;
    final static Pattern verilogIntPattern = Pattern.compile("([0-9]*)'([bdho])?([A-Za-z0-9_]+)");

    IntValue(long x) {
	value = x;
	width = 0;
    }
    IntValue(long x, int width) {
	value = x;
	this.width = 0;
    }

    void tryMatch(String pat, String x) {
	logger.fine(String.format("Match %s %s %s", pat, x, Pattern.matches(pat, x)));
    }

    IntValue(String x) {
	Matcher m = verilogIntPattern.matcher(x);
	if (m.matches()) {
	    String widthspec = m.group(1);
	    String basespec = m.group(2);
	    int base = 10;
	    if (basespec.equals("b")) {
		base = 2;
	    } else if (basespec.equals("o")) {
		base = 8;
	    } else if (basespec.equals("h")) {
		base = 16;
	    } else if (basespec.equals("d")) {
		base = 10;
	    } else {
		logger.fine(String.format("Parsing integer %s basespec %s", x, basespec));
		assert basespec.length() == 0;
		base = 10;
	    }
	    if (widthspec.length() > 0)
		width = Integer.parseInt(widthspec);
	    else
		width = 0;
	    String digits = m.group(3);
	    digits = digits.replace("_", "");
	    value = Long.parseLong(digits, base);
	} else {
	    value = Integer.parseInt(x);
	    width = 0;
	}
    }

    @Override
    public Value unop(String op) {
        //FIXME
        return (Value)this;
    }
    @Override
    public Value binop(String op, Value other) {
        long ov = ((IntValue)other).value;
        if (op.equals("==")) {
            return new BoolValue(value == ov);
        } else if (op.equals("!=")) {
            return new BoolValue (value != ov);
        } else if (op.equals("<")) {
            return new BoolValue(value < ov);
        } else if (op.equals("<=")) {
            return new BoolValue(value <= ov);
        } else if (op.equals(">")) {
            return new BoolValue(value > ov);
        } else if (op.equals(">=")) {
            return new BoolValue(value >= ov);
        } else if (op.equals("+")) {
            return new IntValue(value + ov);
        } else if (op.equals("-")) {
            return new IntValue(value - ov);
        } else if (op.equals("*")) {
            return new IntValue(value * ov);
        } else if (op.equals(">>")) {
            return new IntValue(value >> ov);
        }
        logger.severe("Unhandled int binop " + op);
        return this;
    }

    public String toString() {
        return String.format("<IntValue %d>", value);
    }
}

class BoolValue extends Value {
    private static Logger logger = Logger.getGlobal();
    final boolean value;
    BoolValue(boolean x) { value = x; }
    @Override
    public Value unop(String op) {
        //FIXME
        return this;
    }
    @Override
    public Value binop(String op, Value other) {
        boolean ov = ((BoolValue)other).value;
        if (op.equals("&&")) {
            return new BoolValue(value && ov);
        } else if (op.equals("||")) {
            return new BoolValue(value || ov);
        }
        logger.severe("Unhandled bool binop " + op);
        return this;
    }

    public String toString() {
        return String.format("<BoolValue %s>", value);
    }
}

class VectorValue extends Value {
    public final ArrayList<Value> value;
    public final int size;
    VectorValue(long size) {
        this.size = (int)size;
        value = new ArrayList<>((int)size);
    }
    public String toString() {
        return String.format("<Vector#(%d)>", size);
    }
    public void update(int i, Value v) {
        value.add(i, v);
    }
    public Value select(int i) {
        return value.get(i);
    }
    public static VectorValue newVector(int size) {
        VectorValue vect = new VectorValue(size);
        return vect;
    }
    public static VectorValue genVector(int size) {
        VectorValue vect = new VectorValue(size);
        for (int i = 0; i < size; i++)
            vect.value.add(i, new IntValue(i));
        return vect;
    }
}

class RegValue extends Value {
    private static Logger logger = Logger.getGlobal();
    final String name;
    Value value;
    Value newValue;
    RegValue(String name, Value initValue) {
        this.name = name;
        value = initValue;
        logger.info(String.format("New register %s with value %s", name, initValue));
    }
    void update(Value v) {
        newValue = v;
    }
    void commit() {
        if (newValue != null) {
            value = newValue;
            newValue = null;
        }
    }
    void abort() {
        newValue = null;
    }
    @Override
    Value read() {
        return value;
    }
    @Override
    public Value sub(Value index) {
        long v = ((IntValue)value).value;
        long i = ((IntValue)index).value;
        return new IntValue((v >> i)  & 1);
    }
    @Override
    public Value sub(Value msb, Value lsb) {
        long v = ((IntValue)value).value;
        long m = ((IntValue)msb).value;
        long l = ((IntValue)lsb).value;
        long mask = (1 << (m - l + 1)) - 1;
        return new IntValue((v >> l) & mask);
    }
}

class FunctionValue extends Value {
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
    FunctionValue(String name, int argCount, SymbolTable context, SymbolTable parentFrame) {
        this.name = name;
        this.function = null;
        this.method = null;
        this.module = null;
        this.context = context;
        this.parentFrame = parentFrame;
        this.argCount = argCount;
        this.functionType = FunctionType.Function;
        args = new ArrayList<>();
    }
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
	@SuppressWarnings("unchecked")
	ArrayList<Value> alv = (ArrayList<Value>)(args.clone());
	nfv.args = alv;
        return nfv;
    }
    int remainingArgCount() {
        return argCount - args.size();
    }
    BSVParser.ProvisosContext provisos() {
	if (function != null)
	    return function.functionproto().provisos();
	if (module != null)
	    return module.moduleproto().provisos();
	if (method != null)
	    return method.provisos();
	return null;
    }
}

class Rule extends Value {
    final public String name;
    final public BSVParser.ExpressionContext guard;
    final public List<BSVParser.StmtContext> body;
    final public SymbolTable context;

    public Rule(String name, BSVParser.RuledefContext ruledef, SymbolTable context) {
        this.name = name;
        if (ruledef.rulecond() != null)
            this.guard = ruledef.rulecond().expression();
        else
            this.guard = null;
        this.body = ruledef.rulebody().stmt();
        this.context = context;
    }
    public String toString() {
        return "Rule-" + name;
    }
}

class ModuleInstance extends Value {
    final String name;
    final BSVParser.ModuledefContext module;
    final SymbolTable context;
    ModuleInstance(String name, BSVParser.ModuledefContext module, SymbolTable context) {
        this.name = name;
        this.module = module;
        this.context = context;
    }
}
