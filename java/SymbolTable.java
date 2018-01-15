
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
    public final SymbolTable parent;

    SymbolTable (SymbolTable parent) {
	this.parent = parent;
	bindings = new TreeMap<String,SymbolTableEntry>();
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

}
