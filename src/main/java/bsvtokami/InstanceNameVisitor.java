package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;
import java.util.logging.Logger;

class InstanceEntry implements java.lang.Comparable {
    public String interfaceName;
    public String methodName;
    public BSVType instanceType;
    public BSVType methodType;
    InstanceEntry() {
    }
    public int compareTo(Object o) {
	InstanceEntry oentry = (InstanceEntry)o;
	//FIXME
	return methodName.compareTo(oentry.methodName);
    }
}

class InstanceNameVisitor extends BSVBaseVisitor<String> {
    private static Logger logger = Logger.getGlobal();
    private SymbolTable scope;
    public TreeMap<String,TreeSet<InstanceEntry>> methodsUsed;
    InstanceNameVisitor(SymbolTable scope) {
        this.scope = scope;
        methodsUsed = new TreeMap<>();
    }

    BSVType dereferenceTypedef(BSVType bsvtype) {
        assert scope != null;
        assert bsvtype != null;
        SymbolTableEntry entry = scope.lookupType(bsvtype.name);
        if (entry != null) {
            //fixme
            return entry.type;
        }
        return bsvtype;
    }

    @Override public String visitOperatorexpr(BSVParser.OperatorexprContext ctx) {
        String instanceName = visit(ctx.binopexpr());
        logger.fine("visitOperatorExpr " + ctx.getRuleIndex() + " " + ctx.getText() + " " + instanceName);
        return instanceName;
    }
    @Override public String visitBinopexpr(BSVParser.BinopexprContext ctx) {
        String instanceName = null;
        if (ctx.unopexpr() != null) {
            instanceName = visit(ctx.unopexpr());
        }
        logger.fine("visitBinopexpr " + ctx.getRuleIndex() + " " + ctx.getText() + " " + instanceName);
        return instanceName;
    }
    @Override public String visitUnopexpr(BSVParser.UnopexprContext ctx) {
        String instanceName = null;
        if (ctx.op == null)
            instanceName = visit(ctx.exprprimary());
        logger.fine("visitUnopexpr " + ctx.getRuleIndex() + " " + ctx.getText() + " " + instanceName);
        return instanceName;
    }
    @Override public String visitCallexpr(BSVParser.CallexprContext ctx) {
        return visit(ctx.fcn);
    }
    @Override public String visitFieldexpr(BSVParser.FieldexprContext ctx) {
        String instanceName = visit(ctx.exprprimary());
        if (instanceName != null) {
            String fieldName = ctx.field.getText();
            String methodName = String.format("%s.%s", instanceName, fieldName);
            SymbolTableEntry entry = scope.lookup(instanceName);
            assert entry != null: "Field expr problem at " + StaticAnalysis.sourceLocation(ctx);
	    BSVType interfaceType = dereferenceTypedef(entry.type);
	    System.err.println(String.format("Type %s interface %s instance %s at %s",
					     entry.type, interfaceType, instanceName, StaticAnalysis.sourceLocation(ctx)));
            SymbolTableEntry interfaceEntry = scope.lookupType(interfaceType.name);
            assert interfaceEntry != null : "No interface entry for " + interfaceType + " at " +  StaticAnalysis.sourceLocation(ctx);

	    assert interfaceEntry.mappings != null: "No interface mappings for " + entry.type.name;
            SymbolTableEntry methodEntry = interfaceEntry.mappings.lookup(fieldName);
	    if (methodEntry == null) {
		for (Map.Entry<String,SymbolTableEntry> mapping: interfaceEntry.mappings.bindings.entrySet()) {
		    System.err.println(String.format("ifc %s method %s type %s", interfaceType.name, mapping.getKey(), mapping.getValue().type));
		}
	    }
	    assert methodEntry != null: String.format("No symbol table entry for method %s of interface %s at %s",
						      fieldName, entry.type.name, StaticAnalysis.sourceLocation(ctx));
	    BSVType instantiatedType = methodEntry.type.instantiate(interfaceType.params, entry.type.params);
	    System.err.println(String.format("    method %s type %s interface type %s",
					     fieldName, instantiatedType, methodEntry.type));

            logger.fine("methodName " + methodName + " " + entry.type + " method type " + methodEntry.type);
            if (!methodsUsed.containsKey(instanceName))
                methodsUsed.put(instanceName, new TreeSet<InstanceEntry>());
	    InstanceEntry instanceEntry = new InstanceEntry();
	    instanceEntry.methodName = fieldName;
	    instanceEntry.methodType = instantiatedType;
	    instanceEntry.interfaceName = interfaceType.name;
	    instanceEntry.instanceType = entry.type;
            methodsUsed.get(instanceName).add(instanceEntry);
            return methodName;
        }
        return null;
    }
    @Override public String visitVarexpr(BSVParser.VarexprContext ctx) {
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
            SymbolTableEntry entry = scope.lookup(varName);
            if (entry != null) {
                if (entry.instanceName != null) {
                    logger.fine(String.format("Instancename %s -> %s", varName, entry.instanceName));
                    return entry.instanceName;
                } else {
                    return varName;
                }
            } else {
                logger.fine(String.format("No symbol table entry for %s", varName));
		return varName;
            }
        }
        return null;
    }
}
