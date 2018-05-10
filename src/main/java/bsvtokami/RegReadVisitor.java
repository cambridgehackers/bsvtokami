package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;
import java.util.logging.Logger;


class RegReadVisitor extends BSVBaseVisitor<Void> {
    public TreeMap<String,BSVType> regs = new TreeMap<>();
    final SymbolTable scope;
    RegReadVisitor(SymbolTable scope) {
        this.scope = scope;
    }

    @Override public Void visitVarexpr(BSVParser.VarexprContext ctx) {
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
            if (scope.containsKey(varName)) {
                SymbolTableEntry entry = scope.lookup(varName);
                if (entry.type.name.equals("Reg")) {
                    regs.put(varName, entry.type.params.get(0));
                }
            }
        }
        return null;
    }
}
