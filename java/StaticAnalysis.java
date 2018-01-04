import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;

    StaticAnalysis() {
        // global table
        symbolTable = new SymbolTable(null);
        scopes = new HashMap<ParserRuleContext, SymbolTable>();
    }

    SymbolTable getScope(ParserRuleContext def) {
        if (scopes.containsKey(def)) {
            return (SymbolTable)scopes.get(def);
        } else {
            return null;
        }
    }

    @Override
    public Void visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {
        String interfaceName = ctx.typedeftype().typeide().getText();
        symbolTable.bind(interfaceName,
                         new SymbolTableEntry(interfaceName, "interface"));

        symbolTable = new SymbolTable(symbolTable);
        scopes.put(ctx, symbolTable);

        visitChildren(ctx);

        return null;
    }

    @Override public Void visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        String typedefname = ctx.upperCaseIdentifier().getText();
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname, "struct"));
        for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String tagname = elt.upperCaseIdentifier().getText();
            symbolTable.bind(tagname, new SymbolTableEntry(tagname, typedefname));
        }
        return null;
    }

    @Override public Void visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        String typedefname = ctx.typedeftype().getText();
        return null;
    }

    @Override public Void visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        String typedefname = ctx.typedeftype().typeide().getText();
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname, "tagged union"));
        for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
            BSVParser.UpperCaseIdentifierContext id = member.upperCaseIdentifier();
            if (id != null) {
                String idname = id.getText();
                symbolTable.bind(idname,
                                 new SymbolTableEntry(idname, typedefname));
            } else if (member.substruct() != null) {
            } else if (member.subunion() != null) {
            }
        }
        return null;
    }

    @Override public Void visitTypeclassdecl(BSVParser.TypeclassdeclContext ctx) {
        symbolTable = new SymbolTable(symbolTable);
        scopes.put(ctx, symbolTable);

        visitChildren(ctx);

        symbolTable = symbolTable.parent;
        return null;
    }

    @Override public Void visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) {
        symbolTable = new SymbolTable(symbolTable);
        scopes.put(ctx, symbolTable);

        visitChildren(ctx);

        symbolTable = symbolTable.parent;
        return null;
    }

    @Override
    public Void visitTypedefsynonym(BSVParser.TypedefsynonymContext ctx) {
        String typedefname = ctx.typedeftype().typeide().getText();
        String type;
        if (ctx.type() != null)
            type = ctx.type().getText();
        else
            type = ctx.functionproto().getText();
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname, type));
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        String modulename = ctx.moduleproto().modulename.getText();
        String interfacename = "Empty";
        BSVParser.ModuleformalargsContext moduleformalargs = ctx.moduleproto().moduleformalargs();
        if (moduleformalargs != null) {
            interfacename = moduleformalargs.type(0).getText();
        }
        symbolTable.bind(modulename,
                         new SymbolTableEntry(modulename, interfacename));
        symbolTable = new SymbolTable(symbolTable);
        scopes.put(ctx, symbolTable);
        visitChildren(ctx);
        symbolTable = symbolTable.parent;
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
        symbolTable = new SymbolTable(symbolTable);
        scopes.put(ruledef, symbolTable);
        visitChildren(ruledef);
        symbolTable = symbolTable.parent;
        return null;
    }


    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
        String typeName = ctx.t.getText();
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
            //System.err.println("VarInit " + typeName + " " + varName);
            symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, typeName));
        }
        return null;
    }

    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
        String typeName = ctx.t.getText();
        String varName = ctx.var.getText();
        //System.err.println("ActionBinding " + typeName + " " + varName);
        symbolTable.bind(ctx.var.getText(), new SymbolTableEntry(varName, typeName));
        return null;
    }

    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        String typeName = "unknown";
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            //System.err.println("VarInit " + typeName + " " + varName);
            //Expression rhs = expressionConverter.visit(ctx.rhs);
            symbolTable.bind(varName, new SymbolTableEntry(varName, typeName));
        }
        return null;
    }
}
