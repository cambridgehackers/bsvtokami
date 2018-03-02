import java.util.*;
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
    final int value;
    IntValue(int x) { value = x;}

    @Override
    public Value unop(String op) {
        //FIXME
        return (Value)this;
    }
    @Override
    public Value binop(String op, Value other) {
        int ov = ((IntValue)other).value;
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
        }
        System.err.println("Unhandled int binop " + op);
        return this;
    }

    public String toString() {
        return String.format("<IntValue %d>", value);
    }
}

class BoolValue extends Value {
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
        System.err.println("Unhandled bool binop " + op);
        return this;
    }

    public String toString() {
        return String.format("<BoolValue %s>", value);
    }
}

class VectorValue extends Value {
    public final ArrayList<Value> value;
    public final int size;
    VectorValue(int size) {
        this.size = size;
        value = new ArrayList<>(size);
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
    final String name;
    Value value;
    Value newValue;
    RegValue(String name, Value initValue) {
        this.name = name;
        value = initValue;
        System.err.println(String.format("New register %s with value %s", name, initValue));
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
        int v = ((IntValue)value).value;
        int i = ((IntValue)index).value;
        return new IntValue((v >> i)  & 1);
    }
    @Override
    public Value sub(Value msb, Value lsb) {
        int v = ((IntValue)value).value;
        int m = ((IntValue)msb).value;
        int l = ((IntValue)lsb).value;
        int mask = (1 << (m - l + 1)) - 1;
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
        nfv.args = (ArrayList<Value>)args.clone();
        return nfv;
    }
    int remainingArgCount() {
        return argCount - args.size();
    }
}

class Rule extends Value {
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