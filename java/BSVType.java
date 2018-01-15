import java.util.*;

class BSVType {
    final public String name;
    public List<BSVType> params;

    BSVType(String name) {
	this.name = name;
	this.params = new ArrayList<BSVType>();
    }
    BSVType(String name, List<BSVType> params) {
	this.name = name;
	this.params = params;
    }	
    public String toString() {
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
}
