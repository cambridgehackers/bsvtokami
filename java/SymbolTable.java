
import java.io.*;
import java.util.*;

class SymbolTableEntry {
    public final String name;
    public final BSVType type;
    SymbolTableEntry(String name, BSVType type) {
	this.name = name;
	this.type = type;
    }
}

class SymbolTable {
    private Map<String,SymbolTableEntry> bindings;
    private Map<String,SymbolTableEntry> typeBindings;
    public final SymbolTable parent;
    public enum ScopeType {
	Package, Module, Action, Declaration
    }
    public final ScopeType scopeType;

    SymbolTable (SymbolTable parent, ScopeType st) {
	this.parent = parent;
	scopeType = st;
	bindings = new TreeMap<String,SymbolTableEntry>();
	typeBindings = new TreeMap<String,SymbolTableEntry>();
    }

    boolean containsKey(String key) {
	if (bindings.containsKey(key)) {
	    return true;
	} else if (parent != null) {
	    return parent.containsKey(key);
	} else {
	    return false;
	}
    }

    SymbolTableEntry lookup(String key) {
	if (bindings.containsKey(key)) {
	    return (SymbolTableEntry)bindings.get(key);
	} else if (parent != null) {
	    return parent.lookup(key);
	} else {
	    return null;
	}
    }

    void bind(String key, SymbolTableEntry entry) {
	System.err.println("binding " + key + " with type " + entry.type);
	bindings.put(key, entry);
    }

    SymbolTableEntry lookupType(String key) {
	if (typeBindings.containsKey(key)) {
	    return (SymbolTableEntry)typeBindings.get(key);
	} else if (parent != null) {
	    return parent.lookup(key);
	} else {
	    return null;
	}
    }

    void bindType(String key, BSVType bsvtype) {
	System.err.println("binding type " + key + " with type " + bsvtype);
	typeBindings.put(key, new SymbolTableEntry(key, bsvtype));
    }

}
