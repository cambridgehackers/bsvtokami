package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;
import java.util.logging.Logger;


class ReturnVisitor extends BSVBaseVisitor<Void> {
    public BSVParser.ReturnexprContext returnExpr;
    final SymbolTable scope;
    ReturnVisitor(SymbolTable scope) {
        this.scope = scope;
    }

    @Override public Void visitReturnexpr(BSVParser.ReturnexprContext ctx) {
        returnExpr = ctx;
        return null;
    }
}
