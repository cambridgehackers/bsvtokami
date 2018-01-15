import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.*;
import java.io.*;

public class StaticAnalysis extends BSVBaseVisitor<Void>
{
    private SymbolTable symbolTable;
    private HashMap<ParserRuleContext, SymbolTable> scopes;
    private BSVTypeVisitor typeVisitor;

    StaticAnalysis() {
        // global table
        symbolTable = new SymbolTable(null);
        scopes = new HashMap<ParserRuleContext, SymbolTable>();
	typeVisitor = new BSVTypeVisitor();
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
                         new SymbolTableEntry(interfaceName,
					      typeVisitor.visit(ctx.typedeftype())));

        symbolTable = new SymbolTable(symbolTable);
        scopes.put(ctx, symbolTable);

        visitChildren(ctx);

        return null;
    }

    @Override public Void visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        String typedefname = ctx.upperCaseIdentifier().getText();
	BSVType enumtype = typeVisitor.visit(ctx);
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname,
					      enumtype));
        for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String tagname = elt.upperCaseIdentifier().getText();
            symbolTable.bind(tagname, new SymbolTableEntry(tagname, enumtype));
        }
        return null;
    }

    @Override public Void visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        String typedefname = ctx.typedeftype().getText();
        return null;
    }

    @Override public Void visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        String typedefname = ctx.typedeftype().typeide().getText();
	BSVType taggeduniontype = typeVisitor.visit(ctx);
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname,
					      taggeduniontype));
        for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
            BSVParser.UpperCaseIdentifierContext id = member.upperCaseIdentifier();
            if (id != null) {
                String idname = id.getText();
                symbolTable.bind(idname, new SymbolTableEntry(idname, taggeduniontype));
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
        BSVType bsvtype;
        if (ctx.bsvtype() != null)
            bsvtype = typeVisitor.visit(ctx.bsvtype());
        else
            bsvtype = typeVisitor.visit(ctx.functionproto());
        symbolTable.bind(typedefname,
                         new SymbolTableEntry(typedefname, bsvtype));
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        String modulename = ctx.moduleproto().name.getText();
        BSVType moduletype = typeVisitor.visit(ctx.moduleproto());
        symbolTable.bind(modulename,
                         new SymbolTableEntry(modulename, moduletype));
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
	BSVType bsvtype = typeVisitor.visit(ctx.t);
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
            //System.err.println("VarInit " + typeName + " " + varName);
            symbolTable.bind(varinit.var.getText(), new SymbolTableEntry(varName, bsvtype));
        }
        return null;
    }

    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
	BSVType bsvtype = typeVisitor.visit(ctx.t);
        String varName = ctx.var.getText();
        //System.err.println("ActionBinding " + typeName + " " + varName);
        symbolTable.bind(ctx.var.getText(), new SymbolTableEntry(varName, bsvtype));
        return null;
    }

    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVType bsvtype = new BSVType("let");
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            //System.err.println("VarInit " + typeName + " " + varName);
            //Expression rhs = expressionConverter.visit(ctx.rhs);
            symbolTable.bind(varName, new SymbolTableEntry(varName, bsvtype));
        }
        return null;
    }
}
