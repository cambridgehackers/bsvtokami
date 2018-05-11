package bsvtokami;

import java.util.*;

class InferenceError extends Exception {
    public InferenceError(String msg) {super(msg);}
}

public class BSVType {
    public String name;
    public boolean numeric;
    public boolean isVar;
    public List<BSVType> params;
    public BSVType instance;

    private static int count = 0;

    private void init(String name, boolean numeric) {
	params = new ArrayList<BSVType>();
	if (name == null) {
	    name = "tvar" + count;
	    count++;
	}
	if (name.equals("void"))
	    name = "Void";
	if (name.equals("int")) {
	    name  = "Int";
	    params.add(new BSVType("32"));
	}
	if (name.equals("bit")) {
	    name  = "Bit";
	    params.add(new BSVType("1"));
	}
	this.numeric = numeric || name.matches("[0-9]+");
	isVar = name.matches("[a-z].*");
	this.name = name;
    }
    BSVType() {
	init(null, false);
    }
    BSVType(String name) {
	init(name, false);
    }
    BSVType(String name, boolean numeric) {
	init(name, numeric);
    }
    BSVType(int num) {
	init(String.format("%d", num), true);
    }
    BSVType(long num) {
	init(String.format("%d", num), true);
    }
    BSVType(String name, List<BSVType> params) {
	init(name, false);
	this.params = params;
    }
    BSVType(String name, BSVType param0) {
	init(name, false);
	this.params.add(param0);
    }
    BSVType(String name, BSVType param0, BSVType param1) {
	init(name, false);
	this.params.add(param0);
	this.params.add(param1);
    }

    private void getFreeVariables(TreeMap<String,BSVType> freeVars) {
	if (isVar) {
	    if (instance != null)
		instance.getFreeVariables(freeVars);
	    else if (!freeVars.containsKey(name))
		freeVars.put(name, this);
	} else {
	    for (BSVType param: params)
		param.getFreeVariables(freeVars);
	}
    }

    public TreeMap<String,BSVType> getFreeVariables() {
	TreeMap<String,BSVType> freeVariables = new TreeMap<>();
	getFreeVariables(freeVariables);
	return freeVariables;
    }

    public BSVType prune() {
	if (isVar && instance != null) {
		instance = instance.prune();
		return instance;
	} else {
	    return this;
	}
    }
    public long asLong() {
	assert numeric : this + " should be numeric " + name.matches("[0-9]+");
	return Long.parseLong(name);
    }

    private BSVType freshrec(BSVType tp, List<BSVType> non_generics, Map<BSVType, BSVType> mappings) {
	    tp = tp.prune();
	    if (tp.isVar) {
		if (non_generics.contains(tp)) {
		    if (!mappings.containsKey(tp)) {
			mappings.put(tp, new BSVType());
		    }
		    return mappings.get(tp);
		} else {
		    return tp;
		}
	    } else {
		List<BSVType> freshparams = new ArrayList<BSVType>();
		for (BSVType p: tp.params)
		    freshparams.add(freshrec(p, non_generics, mappings));
		return new BSVType(tp.name, freshparams);
	    }
	}

    public BSVType fresh(List<BSVType> non_generics) {
	Map<BSVType,BSVType> mappings = new HashMap<>();
	return freshrec(this, non_generics, mappings);
    }
    public void unify(BSVType t) throws InferenceError {
	// BSVType a = prune();
	// BSVType b = t.prune();
	// if (a.isVar) {
	//     if (a.occurs_in(b)) {
	// 	throw new InferenceError("recursive unification\n");
	//     }
	//     a.instance = b;
	// } else if (b.isVar) {
	//     b.unify(a);
	// } else {
	//     if (!a.name.equals(b.name)) {
	// 	if (a.name.equals("Reg")) {
	// 	    a.params.get(0).unify(b);
	// 	    return;
	// 	}
	// 	if (b.name.equals("Reg")) {
	// 	    b.params.get(0).unify(a);
	// 	    return;
	// 	}
	//     }
	//     if ((a.name.equals("Reg") || b.name.equals("Reg"))
	// 	&& !a.name.equals(b.name)) {
	// 	// FIXME
	//     }
	//     if (!a.name.equals(b.name)
	// 	|| a.params.size() != b.params.size()
	// 	) {
	// 	throw new InferenceError("Type mismatch (" + a + ") with (" + b + ")");
	//     }
	//     for (int i = 0; i < a.params.size(); i++) {
	// 	a.params.get(i).unify(b.params.get(i));
	//     }
	// }
    }
    public boolean occurs_in(BSVType b) {
	b = b.prune();
	if (this == b) {
	    return true;
	} else if (!b.isVar) {
	    for (BSVType bparam: b.params) {
		if (this.occurs_in(bparam))
		    return true;
	    }
	}
	return false;
    }

    public String toString() {
	if (instance != null)
	    return instance.toString();
	if (name.equals("Function")) {
	    String result = "";
	    BSVType p0 = params.get(0);
	    assert p0 != null;
	    assert p0.name != null;
	    if (p0.name.equals("Function"))
		result += "(" + p0.toString() + ")";
	    else
		result += p0.toString();
	    return result + " -> " + params.get(1);
	}

	String result = name;
	if (params.size() > 0) {
	    result = name + "#(";
	    String sep = "";
	    for (BSVType p: params) {
		result += sep;
		result += p.toString();
		sep = ", ";
	    }
	    result += ")";
	}
	return result;
    }

    public static void main(String[] argv) {
	System.out.println("testing type inference\n");
	BSVType tp1 = new BSVType("Function",
				  new BSVType("Int"), new BSVType("Int"));
	BSVType tp2 = new BSVType("Bit", new BSVType("3"));
	BSVType tp3 = new BSVType("Bit", new BSVType());
	try {
	    tp1.unify(tp1);
	    tp2.unify(tp3);
	    System.out.println("tp2: " + tp2.prune());
	    System.out.println("tp3: " + tp3.prune());
	    tp1.unify(tp2);
	} catch (InferenceError e) {
	    System.err.println("InferenceError: " + e);
	}
    }
}
