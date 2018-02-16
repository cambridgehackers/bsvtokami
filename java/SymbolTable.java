
import java.io.*;
import java.util.*;

class SymbolTableEntry {
    public final String name;
    public final BSVType type;
    public SymbolTable mappings; // for interfaces
    public Value value;
    public String instanceName;
    public String pkgName;
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
}

class SymbolTable {
    public final Map<String,SymbolTableEntry> bindings;
    public final Map<String,SymbolTableEntry> typeBindings;
    public final SymbolTable parent;
    public enum ScopeType {
        Package, Module, Action, Declaration, Block
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
        System.err.println("binding " + key + " with type " + entry.type + " in scope " + this);
        bindings.put(key, entry);
    }
    void bind(String pkgName, String key, SymbolTableEntry entry) {
        System.err.println("binding " + key + " with type " + entry.type + " in scope " + this);
        entry.pkgName = pkgName;
        bindings.put(key, entry);
    }

    SymbolTableEntry lookupType(String key) {
        if (typeBindings.containsKey(key)) {
            return (SymbolTableEntry)typeBindings.get(key);
        } else if (parent != null) {
            return parent.lookupType(key);
        } else {
            return null;
        }
    }

    void bindType(String key, BSVType bsvtype) {
        System.err.println("binding type " + key + " with type " + bsvtype);
        SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        typeBindings.put(key, entry);
    }
    void bindType(String pkgName, String key, BSVType bsvtype) {
        System.err.println("binding type " + key + " with type " + bsvtype);
        SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        entry.pkgName = pkgName;
        typeBindings.put(key, entry);
    }
    void bindType(String pkgName, String key, BSVType bsvtype, SymbolTable mappings) {
        System.err.println("binding type " + key + " with type " + bsvtype);
        SymbolTableEntry entry = new SymbolTableEntry(key, bsvtype);
        entry.mappings = mappings;
        entry.pkgName = pkgName;
        typeBindings.put(key, entry);
    }
    SymbolTable copy(SymbolTable parentContext) {
        SymbolTable n = new SymbolTable(parentContext, scopeType);
        for (Map.Entry<String,SymbolTableEntry> entry: bindings.entrySet()) {
            n.bindings.put(entry.getKey(), entry.getValue().copy());
            System.err.println("    copy " + entry.getKey() + " " + entry.getValue());
        }
        for (Map.Entry<String,SymbolTableEntry> entry: typeBindings.entrySet()) {
            n.typeBindings.put(entry.getKey(), entry.getValue().copy());
            System.err.println("    copy " + entry.getKey() + " " + entry.getValue());
        }
        return n;
    }
}
