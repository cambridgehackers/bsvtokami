import java.util.*;

class InferenceError extends Exception {
    public InferenceError(String msg) {super(msg);}
}

public class BSVType {
    final public String name;
    final public boolean numeric;
    final public boolean isVar;
    public List<BSVType> params;
    public BSVType instance;

    private static int count = 0;

    BSVType() {
	name = "tvar-" + count;
	count++;
	this.params = new ArrayList<BSVType>();
	numeric = false;
	isVar = true;
    }
    BSVType(String name) {
	this.name = name;
	this.params = new ArrayList<BSVType>();
	numeric = false;
	isVar = name.matches("^[a-z]");
    }
    BSVType(String name, boolean numeric) {
	this.name = name;
	this.params = new ArrayList<BSVType>();
	this.numeric = numeric;
	isVar = name.matches("^[a-z]");
    }
    BSVType(String name, List<BSVType> params) {
	this.name = name;
	this.params = params;
	numeric = false;
	isVar = false;
    }
    BSVType(String name, BSVType param0) {
	this.name = name;
	this.params = new ArrayList<>();
	this.params.add(param0);
	numeric = false;
	isVar = false;
    }
    BSVType(String name, BSVType param0, BSVType param1) {
	this.name = name;
	this.params = new ArrayList<>();
	this.params.add(param0);
	this.params.add(param1);
	numeric = false;
	isVar = false;
    }
    public BSVType prune() {
	if (isVar && instance != null) {
		instance = instance.prune();
		return instance;
	} else {
	    return this;
	}
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
	BSVType a = prune();
	BSVType b = t.prune();
	if (a.isVar) {
	    if (a.occurs_in(b)) {
		throw new InferenceError("recursive unification\n");
	    }
	    a.instance = b;
	} else if (b.isVar) {
	    b.unify(a);
	} else {
	    if (!a.name.equals(b.name)
		|| a.params.size() != b.params.size()
		) {
		throw new InferenceError("Type mismatch (" + a + ") with (" + b + ")");
	    }
	    for (int i = 0; i < a.params.size(); i++) {
		a.params.get(i).unify(b.params.get(i));
	    }
	}
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
