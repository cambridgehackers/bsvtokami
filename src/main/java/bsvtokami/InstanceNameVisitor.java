package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;
import java.util.logging.Logger;

class InstanceNameVisitor extends BSVBaseVisitor<String> {
    private static Logger logger = Logger.getGlobal();
    private SymbolTable scope;
    public TreeMap<String,TreeSet<SymbolTableEntry>> methodsUsed;
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
            assert entry != null;
	    BSVType interfaceType = dereferenceTypedef(entry.type);
            SymbolTableEntry interfaceEntry = scope.lookupType(interfaceType.name);
            assert interfaceEntry != null : "No interface entry for " + interfaceType + " at " +  StaticAnalysis.sourceLocation(ctx);

	    assert interfaceEntry.mappings != null: "No interface mappings for " + entry.type.name;
            SymbolTableEntry methodEntry = interfaceEntry.mappings.lookup(fieldName);
	    assert methodEntry != null: String.format("No symbol table entry for method %s of interface %s", fieldName, entry.type.name);
            logger.fine("methodName " + methodName + " " + entry.type + " method type " + methodEntry.type);
            if (!methodsUsed.containsKey(instanceName))
                methodsUsed.put(instanceName, new TreeSet<SymbolTableEntry>());
            methodsUsed.get(instanceName).add(methodEntry);
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
            }
        }
        return null;
    }
}
