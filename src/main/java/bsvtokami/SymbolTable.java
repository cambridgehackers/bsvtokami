package bsvtokami;

import java.io.*;
import java.util.*;
import java.util.logging.Logger;

class SymbolTableEntry implements java.lang.Comparable {
    public final String name;
    public BSVType type;
    SymbolType symbolType;
    public SymbolTable mappings; // for interfaces, tagged unions
    public ArrayList<SymbolTableEntry> instances; // for type classes
    public Value value;
    public String instanceName;
    public String pkgName;
    public SymbolTableEntry parent; // which interface a method belongs to, etc.
    SymbolTableEntry(String name, BSVType type) {
        this.name = name;
        this.type = type;
    }
    public SymbolTableEntry copy() {
        return new SymbolTableEntry(name, type);
    }
    public void setValue(Value v) {
        value = v;
    }
    public void addInstance(SymbolTableEntry instanceEntry) {
	if (instances == null)
	    instances = new ArrayList<>();
	instances.add(instanceEntry);
    }
    public int compareTo(Object o) {
	SymbolTableEntry oentry = (SymbolTableEntry)o;
	return name.compareTo(oentry.name);
    }
    public SymbolTableEntry setSymbolType(SymbolType st) {
	symbolType = st;
	return this;
    }
}

class SymbolTable {
    private static Logger logger = Logger.getGlobal();

    public final String name;
    public final Map<String,SymbolTableEntry> bindings;
    public final Map<String,SymbolTableEntry> typeBindings;
    public final SymbolTable parent;
    public enum ScopeType {
        Package, Module, Action, Declaration, Block, TypeClassInstance, IfStmt, CaseStmt, Loop, TaggedUnion
    }
    public final ScopeType scopeType;

    SymbolTable (SymbolTable parent, ScopeType st) {
        this.parent = parent;
	this.name = "";
        scopeType = st;
        bindings = new TreeMap<String,SymbolTableEntry>();
        typeBindings = new TreeMap<String,SymbolTableEntry>();
    }

    SymbolTable (SymbolTable parent, ScopeType st, String name) {
        this.parent = parent;
	this.name = name;
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

    void unbind(String key) {
	bindings.remove(key);
    }
    SymbolTableEntry bind(String key, BSVType bsvtype) {
        logger.fine("binding " + key + " with type " + bsvtype + " in scope " + this + " " + this.name);
	assert !bindings.containsKey(key)
	    : String.format("Symbol %s already bound in scope %s %s", key, name, this);
	SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        bindings.put(key, entry);
	return entry;
    }
    SymbolTableEntry bind(String key, SymbolTableEntry entry) {
        logger.fine("binding " + key + " with type " + entry.type + " in scope " + this + " " + this.name);
	assert !bindings.containsKey(key)
	    : String.format("Symbol %s already bound in scope %s %s", key, name, this);
        bindings.put(key, entry);
	return entry;
    }
    SymbolTableEntry bind(String pkgName, String key, SymbolTableEntry entry) {
        logger.fine("binding " + key + " with type " + entry.type + " in scope " + this + " " + this.name);
	assert !bindings.containsKey(key)
	    : String.format("Symbol %s::%s already bound in scope %s %s", pkgName, key, name, this);
        entry.pkgName = pkgName;
        bindings.put(key, entry);
	return entry;
    }

    SymbolTableEntry lookupType(String key) {
        if (typeBindings.containsKey(key)) {
            return (SymbolTableEntry)typeBindings.get(key);
        } else if (parent != null) {
	    //logger.fine("lookupType chaining to parent " + parent);
            return parent.lookupType(key);
        } else {
            return null;
        }
    }

    SymbolTableEntry bindType(String key, SymbolTableEntry entry) {
        logger.fine("binding type " + key + " with entry " + entry);
        typeBindings.put(key, entry);
	return entry;
    }
    SymbolTableEntry bindType(String key, BSVType bsvtype) {
        logger.fine("binding type " + key + " with type " + bsvtype + " in scope " + this + " " + this.name);
        SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        typeBindings.put(key, entry);
	return entry;
    }
    SymbolTableEntry bindType(String pkgName, String key, BSVType bsvtype) {
        logger.fine("binding type " + key + " with type " + bsvtype);
        SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        entry.pkgName = pkgName;
        typeBindings.put(key, entry);
	return entry;
    }
    SymbolTableEntry bindType(String pkgName, String key, BSVType bsvtype, SymbolTable mappings) {
        SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        logger.fine("binding type " + key + " with type " + bsvtype + " and mappings " + mappings
			   + " in scope " + this + " " + this.name);
        entry.mappings = mappings;
        entry.pkgName = pkgName;
        typeBindings.put(key, entry);
	return entry;
    }
    SymbolTable copy(SymbolTable parentContext) {
        SymbolTable n = new SymbolTable(parentContext, scopeType);
        for (Map.Entry<String,SymbolTableEntry> entry: bindings.entrySet()) {
            n.bindings.put(entry.getKey(), entry.getValue().copy());
            logger.fine("    copy " + entry.getKey() + " " + entry.getValue());
        }
        for (Map.Entry<String,SymbolTableEntry> entry: typeBindings.entrySet()) {
            n.typeBindings.put(entry.getKey(), entry.getValue().copy());
            logger.fine("    copy " + entry.getKey() + " " + entry.getValue());
        }
        return n;
    }
}
