package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;
import java.util.logging.Logger;

class CallVisitor extends BSVBaseVisitor<BSVParser.CallexprContext> {
    @Override public BSVParser.CallexprContext visitCallexpr(BSVParser.CallexprContext ctx) { return ctx; }
}
class InstanceNameVisitor extends BSVBaseVisitor<String> {
    private static Logger logger = Logger.getGlobal();
    private SymbolTable scope;
    public TreeMap<String,TreeSet<SymbolTableEntry>> methodsUsed;
    InstanceNameVisitor(SymbolTable scope) {
        this.scope = scope;
        methodsUsed = new TreeMap<>();
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
            SymbolTableEntry interfaceEntry = scope.lookupType(entry.type.name);
            assert interfaceEntry != null;
            SymbolTableEntry methodEntry = interfaceEntry.mappings.lookup(fieldName);
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
                if (entry.type.name.startsWith("Reg")) {
                    regs.put(varName, entry.type.params.get(0));
                }
            }
        }
        return null;
    }
}


public class BSVToKami extends BSVBaseVisitor<Void>
{
    private static Logger logger = Logger.getGlobal();
    private final File ofile;
    private PrintStream printstream;
    private final StaticAnalysis scopes;
    private SymbolTable scope;
    private String pkgName;
    private Package pkg;
    private ModuleDef moduleDef;
    private ArrayList<String> instances;
    private boolean actionContext;
    private boolean stmtEmitted;
    private boolean inModule;

    BSVToKami(String pkgName, File ofile, StaticAnalysis scopes) {
        this.scopes = scopes;
        this.pkgName = pkgName;
        this.ofile = ofile;
        pkg = new Package(pkgName);
        actionContext = false;
        inModule = false;
        try {
            printstream = new PrintStream(ofile);
        } catch (FileNotFoundException ex) {
            logger.severe(ex.toString());
            printstream = null;
        }
    }

    @Override
    public Void visitPackagedef(BSVParser.PackagedefContext ctx) {
        logger.fine("Package " + pkgName);

        printstream.println("Require Import Bool String List Arith.");
        printstream.println("Require Import Kami.");
        printstream.println("Require Import Lib.Indexer.");
        printstream.println("Require Import Bsvtokami.");
        printstream.println("");
        printstream.println("Require Import FunctionalExtensionality.");
        printstream.println("");
        printstream.println("Set Implicit Arguments.");
        printstream.println("");
        printstream.println();

        scope = scopes.pushScope(ctx);

        if (ctx.packagedecl() != null) {
            if (!pkgName.equals(ctx.packagedecl().pkgname.getText())) {
                logger.fine("Expected " + pkgName + " found " + ctx.packagedecl().pkgname.getText());
            }
        }
        visitChildren(ctx);
        scopes.popScope();
        return null;
    }

    @Override public Void visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) {
        scope = scopes.pushScope(ctx);
        visitChildren(ctx);
        scope = scopes.popScope();
        return null;
    }

    void declareSubstruct(ArrayList<String> members, String fieldPrefix,
                          BSVParser.SubstructContext substruct) {
        for (BSVParser.StructmemberContext member: substruct.structmember()) {
            assert member.subunion() == null;
            if (member.bsvtype() != null) {
                members.add(String.format("    \"%s$%s\" :: %s",
                                          fieldPrefix,
                                          member.lowerCaseIdentifier().getText(),
                                          bsvTypeToKami(member.bsvtype())));
            }
        }
    }

    @Override public Void visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        //scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        String typeName = ctx.typedeftype().typeide().getText();
        System.err.println(String.format("BSVTOKAMI typedef struct %s\n", typeName));
        assert ctx.typedeftype().typeformals() == null;
        printstream.println(String.format("Definition %sFields := (STRUCT {", typeName));
        ArrayList<String> members = new ArrayList<>();
        for (BSVParser.StructmemberContext member: ctx.structmember()) {
            assert member.subunion() == null;
            if (member.bsvtype() != null) {
                members.add(String.format("    \"%s\" :: %s",
                                          member.lowerCaseIdentifier().getText(),
                                          bsvTypeToKami(member.bsvtype())));
            } else {
            }
        }
        printstream.print(String.join(";\n", members));
        printstream.println("}).");
        printstream.println(String.format("Definition %s := (Struct %sFields).", typeName, typeName));
        printstream.println("");

        //scope = scopes.popScope();
        inModule = wasInModule;
        return null;
    }

    @Override public Void visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        //scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        String typeName = ctx.upperCaseIdentifier().getText();
        System.err.println(String.format("BSVTOKAMI typedef enum %s\n", typeName));
        printstream.println(String.format("Definition %sFields := (STRUCT { \"$tag\" :: (Bit 8) }).", typeName));
        printstream.println(String.format("Definition %s := (Struct %sFields).", typeName, typeName));

        String typedefname = ctx.upperCaseIdentifier().getText();
        for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String basetagname = elt.upperCaseIdentifier().getText();
            long tagCount = 1;
            boolean numbered = false;
            long tagFrom = 0;

            System.err.println(String.format("enum %s from %s to %s",
                                             basetagname,
                                             ((elt.from != null) ? elt.from.getText() : ""),
                                             ((elt.to != null) ? elt.to.getText() : "")));
            if (elt.from != null) {
                numbered = true;
                tagCount = Long.parseLong(elt.from.getText());
                if (elt.to != null) {
                    tagFrom = tagCount;
                    tagCount = Long.parseLong(elt.to.getText()) - tagFrom + 1;
                }
            }

            for (int i = 0; i < tagCount; i++) {
                String tagname = basetagname;
                if (numbered) {
                    tagname = String.format("%s%d", basetagname, tagFrom + i);
                }
                SymbolTableEntry entry = scope.lookup(tagname);
                assert entry != null;
                assert entry.value != null;
                IntValue tagValue = (IntValue)entry.value;
                assert tagValue != null;
                printstream.println(String.format("Notation %s := (STRUCT { \"$tag\" ::= $%d })%%kami_expr.",
                                                  tagname, tagValue.value));
            }
        }

        //scope = scopes.popScope();
        inModule = wasInModule;
        return null;
    }
    @Override public Void visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        //scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        String typeName = ctx.typedeftype().typeide().getText();
        System.err.println(String.format("BSVTOKAMI typedef tagged union %s\n", typeName));
        assert ctx.typedeftype().typeformals() == null;
        printstream.println(String.format("Definition %sFields := (STRUCT {", typeName));
        ArrayList<String> members = new ArrayList<>();
        members.add(String.format("    \"$tag\" :: (Bit 8)"));
        for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
            assert member.subunion() == null;
            if (member.bsvtype() != null) {
                members.add(String.format("    \"%s\" :: %s",
                                          member.upperCaseIdentifier().getText(),
                                          bsvTypeToKami(member.bsvtype())));
            } else if (member.substruct() != null) {
                String memberName = member.upperCaseIdentifier().getText();
                declareSubstruct(members, memberName, member.substruct());
            } else {
            }
        }
        printstream.print(String.join(";\n", members));
        printstream.println("}).");
        printstream.println(String.format("Definition %s := (Struct %sFields).", typeName, typeName));
        //scope = scopes.popScope();
        inModule = wasInModule;
        return null;
    }

    @Override public Void visitModuledef(BSVParser.ModuledefContext ctx) {
        for (BSVParser.AttributeinstanceContext attrinstance: ctx.attributeinstance()) {
            for (BSVParser.AttrspecContext attr: attrinstance.attrspec()) {
                if (attr.identifier().getText().equals("nogen"))
                return null;
            }
        }
        instances = new ArrayList<>();
        scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        BSVParser.ModuleprotoContext moduleproto = ctx.moduleproto();
        String moduleName = moduleproto.name.getText();
        String sectionName = moduleName.startsWith("mk") ? moduleName.substring(2) : moduleName;
        moduleDef = new ModuleDef(moduleName);
        pkg.addStatement(moduleDef);
        InstanceNameVisitor inv = new InstanceNameVisitor(scope);
        inv.visit(ctx);

        logger.fine("module " + moduleName);
        printstream.println("Section " + sectionName + ".");
        printstream.println("    Variable moduleName: string.");
        printstream.println("    Local Notation \"^ s\" := (moduleName -- s) (at level 0).");

        if (moduleproto.methodprotoformals() != null) {
            for (BSVParser.MethodprotoformalContext formal : moduleproto.methodprotoformals().methodprotoformal()) {
                if (formal.name != null)
                    printstream.println(String.format("    Variable %sName: string.", formal.name.getText()));
            }
        }

        for (Map.Entry<String,TreeSet<SymbolTableEntry>> entry: inv.methodsUsed.entrySet()) {
            String instanceName = entry.getKey();
            TreeSet<SymbolTableEntry> methods = entry.getValue();
            for (SymbolTableEntry methodEntry: methods) {
                String method = methodEntry.name;
                BSVType methodType = methodEntry.type;
                BSVType argType = methodType.params.get(0);
                BSVType returnType = methodType.params.get(1);
                printstream.println(String.format("    Definition %1$s%2$s := MethodSig (%1$sName--\"%2$s\") (%3$s) : %4$s.",
                                                  instanceName, method, bsvTypeToKami(argType), bsvTypeToKami(returnType)));
            }
        }

        printstream.println("    Definition " + moduleName + "Module := (BKMODULE {" + "\n");
        String stmtPrefix = "    ";
        for (BSVParser.ModulestmtContext modulestmt: ctx.modulestmt()) {
            stmtEmitted = true;
            printstream.print(stmtPrefix);
            visit(modulestmt);
            if (stmtEmitted)
                stmtPrefix = "    with ";
        }
        printstream.println("    }). (*" + ctx.moduleproto().name.getText() + " *)" + "\n");

        if (instances.size() > 0)
            printstream.println(String.format("    Definition %sInstances := (%s)%%kami.",
                                             moduleName,
                                             String.join("\n            ++ ", instances)));

        printstream.print(String.format("    Definition %1$s := (", moduleName));
        if (instances.size() > 0)
            printstream.print(String.format("%1$sInstances ++ ",
                                            moduleName));
        printstream.println(String.format("%1$sModule)%%kami.", moduleName));

        printstream.println("End " + sectionName + ".");
        scope = scopes.popScope();
        moduleDef = null;
        logger.fine("endmodule : " + moduleName);
        inModule = wasInModule;
        return null;
    }

    BSVParser.CallexprContext getCall(ParserRuleContext ctx) {
        return new CallVisitor().visit(ctx);
    }

    @Override public Void visitVarBinding(BSVParser.VarBindingContext ctx) {
        BSVParser.BsvtypeContext t = ctx.t;
        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
            String varName = varinit.var.getText();
            assert scope != null : "No scope to evaluate var binding " + ctx.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            BSVParser.ExpressionContext rhs = varinit.rhs;
            if (rhs != null) {
                BSVParser.CallexprContext call = getCall(rhs);
                if (call != null) {
                    printstream.print(String.format("        Call %s <- ", varName));
                } else {
                    printstream.print(String.format("        LET %s : %s <- ", varName, bsvTypeToKami(t)));
                }
                visit(rhs);
            } else {
                assert false;
                printstream.print(String.format("        LET %s : %s", varName, bsvTypeToKami(t)));
            }
            printstream.println(";");
        }
        return null;
    }
    @Override public Void visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVParser.ExpressionContext rhs = ctx.rhs;
        BSVParser.CallexprContext call = getCall(rhs);
        assert ctx.lowerCaseIdentifier().size() == 1;
        printstream.print(String.format("        %s ",
                                        (call != null) ? "Call" : "Let"));
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            assert entry != null : String.format("No entry for %s at %s",
                                                 varName, StaticAnalysis.sourceLocation(ctx));
            printstream.print(varName);
        }
        if (ctx.op != null) {
            printstream.print(String.format(" %s ", (call != null) ? "<-" : ctx.op.getText()));
            visit(ctx.rhs);
        }
        return null ;
    }
    @Override public Void visitActionBinding(BSVParser.ActionBindingContext ctx) {
        String typeName = ctx.t.getText();
        String varName = ctx.var.getText();
        BSVParser.ExpressionContext rhs = ctx.rhs;
        SymbolTableEntry entry = scope.lookup(varName);
	assert entry != null: "Null var name in " + ctx.getText();
        BSVType bsvtype = entry.type;
        InstanceNameVisitor inv = new InstanceNameVisitor(scope);
        String calleeInstanceName = inv.visit(ctx.rhs);
        if (calleeInstanceName != null && actionContext)
            calleeInstanceName = calleeInstanceName.replace(".", "");

        if (typeName.startsWith("Reg")) {
            BSVType paramtype = bsvtype.params.get(0);
            printstream.print("Register ^\"" + varName + "\" : " + bsvTypeToKami(paramtype)
                             + " <- ");

            BSVParser.CallexprContext call = getCall(ctx.rhs);
            if (call != null && call.fcn != null && call.fcn.getText().equals("mkReg")) {
                printstream.print("$" + call.expression().get(0).getText());
            } else {
                visit(ctx.rhs);
            }

            printstream.println("");
        } else if (calleeInstanceName != null && actionContext) {
            printstream.println(String.format("        Call %s <- %s(); (* method call 1 *)", varName, calleeInstanceName));
        } else if (!actionContext) {
            printstream.println(String.format("        (* instantiate %s *)", varName));
            stmtEmitted = false;

            String instanceName = String.format("%s", varName); //FIXME concat methodName
            entry.instanceName = instanceName;

            BSVParser.CallexprContext call = getCall(ctx.rhs);
            instances.add(String.format("%s(\"%s\")",
                                        call.fcn.getText(),
                                        instanceName));
        } else {
            printstream.print(String.format("        Call %s <- %s(", varName, calleeInstanceName));
            logger.fine("generic call " + ctx.rhs.getRuleIndex() + " " + ctx.rhs.getText());
            BSVParser.CallexprContext call = getCall(ctx.rhs);
            String sep = "";
            for (BSVParser.ExpressionContext expr: call.expression()) {
                printstream.print(sep);
                visit(expr);
                sep = ", ";
            }
            printstream.println("); (* method call 2 *)");
        }
        return null;
    }

    @Override public Void visitRuledef(BSVParser.RuledefContext ruledef) {
        boolean outerContext = actionContext;
        actionContext = true;
        scope = scopes.pushScope(ruledef);
        String ruleName = ruledef.name.getText();
        RuleDef ruleDef = new RuleDef(ruleName);
        BSVParser.RulecondContext rulecond = ruledef.rulecond();
        moduleDef.addRule(ruleDef);

        printstream.println("Rule ^\"" + ruleName + "\" :=");
        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        if (rulecond != null) regReadVisitor.visit(rulecond);
        for (BSVParser.StmtContext stmt: ruledef.rulebody().stmt()) {
            regReadVisitor.visit(stmt);
        }
        for (Map.Entry<String,BSVType> entry: regReadVisitor.regs.entrySet()) {
            String regName = entry.getKey();
            printstream.println("        Read " + regName + "_v : " + bsvTypeToKami(entry.getValue()) + " <- ^\"" + regName + "\";");
        }

        if (rulecond != null) {
            printstream.print("        Assert(");
            visit(rulecond);
            printstream.println(");");
        }
        for (BSVParser.StmtContext stmt: ruledef.rulebody().stmt()) {
            visit(stmt);
        }
        printstream.println("        Retv (* rule " + ruledef.name.getText() + " *)" + "\n");
        scope = scopes.popScope();
        actionContext = outerContext;
        return null;
    }

    @Override public Void visitFunctiondef(BSVParser.FunctiondefContext ctx) {
        scope = scopes.pushScope(ctx);
        BSVParser.FunctionprotoContext functionproto = ctx.functionproto();
        printstream.print(String.format("Definition %s", functionproto.name.getText()));
        if (functionproto.methodprotoformals() != null) {
            for (BSVParser.MethodprotoformalContext formal: functionproto.methodprotoformals().methodprotoformal()) {
                BSVParser.BsvtypeContext bsvtype = formal.bsvtype();
                String varName = formal.name.getText();
                printstream.print(String.format(" (%s: %s)", varName, bsvTypeToKami(bsvtype)));
            }
        }
        String returntype = (functionproto.bsvtype() != null) ? bsvTypeToKami(functionproto.bsvtype()) : "";
        printstream.println(String.format(": %s := ", returntype));

        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        if (ctx.expression() != null) {
            printstream.print("    ");
            regReadVisitor.visit(ctx.expression());

        if (ctx.expression() != null)
            visit(ctx.expression());
        } else {

            for (Map.Entry<String,BSVType> entry: regReadVisitor.regs.entrySet()) {
                String regName = entry.getKey();
                printstream.println("        Read " + regName + "_v : " + bsvTypeToKami(entry.getValue()) + " <- \"" + regName + "\";");
            }
            for (BSVParser.StmtContext stmt: ctx.stmt())
                regReadVisitor.visit(stmt);
            for (BSVParser.StmtContext stmt: ctx.stmt())
                visit(stmt);

            if (returntype.equals("Action") || returntype.equals("Void"))
                printstream.println("        Retv");
        }
        printstream.println(".");
        printstream.println("");
        scope = scopes.popScope();
        return null;
    }

    @Override public Void visitMethoddef(BSVParser.MethoddefContext ctx) {
        boolean outerContext = actionContext;
        actionContext = true;

        String methodName = ctx.name.getText();
        printstream.print("Method ^\"" + methodName + "\" (");
        if (ctx.methodformals() != null) {
            String sep = "";
            for (BSVParser.MethodformalContext formal: ctx.methodformals().methodformal()) {
                BSVParser.BsvtypeContext bsvtype = formal.bsvtype();
                String varName = formal.name.getText();
                printstream.print(sep + varName + ": " + bsvTypeToKami(bsvtype));
                sep = ", ";
            }
        }
        String returntype = (ctx.bsvtype() != null) ? bsvTypeToKami(ctx.bsvtype()) : "";
        printstream.println(") : " + returntype + " := ");
        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        for (BSVParser.StmtContext stmt: ctx.stmt())
            regReadVisitor.visit(stmt);
        if (ctx.expression() != null)
            regReadVisitor.visit(ctx.expression());

        for (Map.Entry<String,BSVType> entry: regReadVisitor.regs.entrySet()) {
            String regName = entry.getKey();
            printstream.println("        Read " + regName + "_v : " + bsvTypeToKami(entry.getValue()) + " <- \"" + regName + "\";");
        }
        for (BSVParser.StmtContext stmt: ctx.stmt())
            visit(stmt);
        if (ctx.expression() != null)
            visit(ctx.expression());

        if (returntype.equals("Action") || returntype.equals("Void"))
            printstream.println("        Retv");
        printstream.println("");
        actionContext = outerContext;
        return null;
    }

    @Override public Void visitRegwrite(BSVParser.RegwriteContext regwrite) {
        printstream.print("        Write ^\"");
        visit(regwrite.lhs);
        printstream.print("\"");
        String regName = regwrite.lhs.getText();
        SymbolTableEntry entry = scope.lookup(regName);
        if (entry != null) {
            printstream.print(" : ");
            printstream.print(bsvTypeToKami(entry.type.params.get(0)));
        }
        printstream.print(" <- ");
        visit(regwrite.rhs);
        printstream.println(";");
        return null;
    }
    @Override public Void visitVarassign(BSVParser.VarassignContext ctx) {
        printstream.print("        Assign ");
        boolean multi = ctx.lvalue().size() > 1;
        int count = 0;
        if (multi) printstream.print("{ ");
        for (BSVParser.LvalueContext lvalue: ctx.lvalue()) {
            if (multi && count > 0) printstream.print(", ");
            printstream.print(lvalue.getText());
            count++;
        }
        if (multi) printstream.print(" }");
        printstream.print(" " + ctx.op.getText() + " ");
        visit(ctx.expression());
        printstream.println(";");
        return null;
    }

    @Override
    public Void visitIfstmt(BSVParser.IfstmtContext ctx) {
        printstream.print("        (If ");
        visit(ctx.expression());
        printstream.println("");
        printstream.print("        then ");
        visit(ctx.stmt(0));
        printstream.print("        Retv;");
        if (ctx.stmt(1) != null) {
            printstream.println("");
            printstream.print("        else ");
            visit(ctx.stmt(1));
            printstream.print("        Retv;");
        }
        printstream.println(")");
        return null;
    }
    void destructurePattern(BSVParser.PatternContext pattern, String match, String tagName) {
        if (pattern.taggedunionpattern() != null) {
            BSVParser.TaggedunionpatternContext taggedunionpattern = pattern.taggedunionpattern();
            if (taggedunionpattern.pattern() != null)
                destructurePattern(taggedunionpattern.pattern(),
                                   match,
                                   taggedunionpattern.tag.getText());
        } else if (pattern.structpattern() != null) {
            BSVParser.StructpatternContext structpattern = pattern.structpattern();
            tagName = structpattern.tag.getText();
            SymbolTableEntry tagEntry = scope.lookup(tagName);
            assert tagEntry != null;
            BSVType tagType = tagEntry.type;
            for (int i = 0; i < structpattern.pattern().size(); i++) {
                String fieldName = structpattern.lowerCaseIdentifier(i).getText();
                BSVParser.PatternContext fieldPattern = structpattern.pattern(i);
                destructurePattern(fieldPattern, String.format("(#%s!%sFields@.\"%s%s%s\")", match,
                                                               bsvTypeToKami(tagType),
                                                               ((tagName != null) ? tagName : ""),
                                                               ((tagName != null) ? "$" : ""),
                                                               fieldName),
                                   null);
            }
        } else if (pattern.lowerCaseIdentifier() != null) {
            printstream.println(String.format("        LET %s <- %s;",
                                              pattern.lowerCaseIdentifier().getText(),
                                              match));
        }
    }

    @Override public Void visitCaseexpr(BSVParser.CaseexprContext ctx) {
        System.err.println("visitCaseexpr");
        return null;
    }
    @Override public Void visitCasestmt(BSVParser.CasestmtContext ctx) {
        int branchnum = 0;
        System.err.println("visitCasestmt");
        logger.fine("visitCasestmt " + ctx.getText());
        for (BSVParser.CasestmtpatitemContext patitem: ctx.casestmtpatitem()) {
            BSVParser.PatternContext pattern = patitem.pattern();
            BSVParser.StructpatternContext structpattern = pattern.structpattern();
            assert structpattern != null;
            String tagName = structpattern.tag.getText();
            SymbolTableEntry tagEntry = scope.lookup(tagName);
            assert tagEntry != null;
            BSVType tagType = tagEntry.type;
            assert tagEntry.value != null : String.format("Missing value for tag %s", tagName);
            IntValue tagValue = (IntValue)tagEntry.value;
            printstream.print("    If (");
            visit(ctx.expression());
            printstream.print(String.format("!%sFields@.\"$tag\"", tagType.name));
            printstream.print(" == ");
            printstream.print(String.format("$%d", tagValue.value));
            printstream.println(") then");
            destructurePattern(pattern, ctx.expression().getText(), null);
            assert patitem.patterncond().expression().size() == 0;
            visit(patitem.stmt());
            printstream.println("        Retv");
            printstream.println("    else");
        }
        printstream.println("        Retv;");
        return null;
    }
    @Override
    public Void visitPattern(BSVParser.PatternContext ctx) {
        //FIXME
        printstream.print("$" + ctx.getText());
        return null;
    }

    @Override public Void visitForstmt(BSVParser.ForstmtContext ctx) {
        scope = scopes.pushScope(ctx);
	BSVParser.FornewinitContext init = ctx.forinit().fornewinit();
	assert init != null : "Only supports new-style for loop init";
	String iterationVar = init.var.getText();
	SymbolTableEntry iterationVarEntry = scope.lookup(iterationVar);
	assert iterationVarEntry != null;
	BSVType iterationVarType = iterationVarEntry.type;
	assert iterationVarType != null;
	assert iterationVarType.name.equals("Integer"): "Iteration var must be an Integer";

	BSVParser.ExpressionContext testExpr = ctx.fortest().expression();
	BSVParser.OperatorexprContext operatorExpr = (testExpr instanceof BSVParser.OperatorexprContext) ? (BSVParser.OperatorexprContext)testExpr : null;
	BSVParser.BinopexprContext binop = operatorExpr.binopexpr();
	assert binop != null;
	assert binop.left != null;
	assert binop.left.getText().equals(iterationVar);
	assert binop.op.getText().equals("<");

	printstream.println("    Let loopM :=");
	printstream.println("      (fix loopM' (limit: nat) (m: nat): InModule :=");
	printstream.println("        match m with");
	printstream.println("        | 0 => NilInModule");
	printstream.println("        | S m' =>");
	printstream.println(String.format("          let %s := limit - m", iterationVar));
	printstream.println("          in STMTSR {");
	visit(ctx.stmt());
	printstream.println("          }");
	printstream.println("          (loopM' limit m')");
	printstream.println("        end).");
        scope = scopes.popScope();
	return null;
    }

    @Override public Void visitBinopexpr(BSVParser.BinopexprContext expr) {
        if (expr.right != null) {
            printstream.print("(");
            if (!inModule) {
                if (expr.op != null) {
                    String op = expr.op.getText();
                    if (op.equals("<"))
                        op = "bitlt";
                    printstream.print(op);
                }
                printstream.print(" ");
            }
            if (expr.left != null)
                visit(expr.left);
            if (inModule) {
                printstream.print(" ");
                printstream.print(expr.op.getText());
                printstream.print(" ");
            } else {
                printstream.print(" ");
            }
            visit(expr.right);
            printstream.print(")");
        } else {
            visitChildren(expr);
        }
        return null;
    }
    @Override public Void visitUnopexpr(BSVParser.UnopexprContext ctx) {
        if (ctx.op != null) {
            printstream.print(ctx.op.getText());
        }
        return visitChildren(ctx);
    }

    @Override public Void visitStructexpr(BSVParser.StructexprContext ctx) {
        printstream.print("STRUCT { ");
        int i = 0;
        for (BSVParser.MemberbindContext memberbind : ctx.memberbinds().memberbind()) {
            printstream.print(String.format("\"%s\" ::= ",
                                            memberbind.field.getText()));
            visit(memberbind.expression());
            printstream.print((i == ctx.memberbinds().memberbind().size() - 1) ? " " : "; ");
            i++;
        }
        printstream.print(" }");
        return null;
    }
    @Override public Void visitTaggedunionexpr(BSVParser.TaggedunionexprContext ctx) {
        printstream.print("STRUCT { ");
        String tagName = ctx.tag.getText();
        SymbolTableEntry tagEntry = scope.lookup(tagName);
        assert tagEntry != null;
        BSVType tagtype = tagEntry.type;
        assert tagEntry.value != null : String.format("Missing value for tag %s", tagName);
        IntValue tagValue = (IntValue)tagEntry.value;
        SymbolTableEntry typedefEntry = scope.lookupType(tagtype.name);
        System.err.println(String.format("tagged union expr %s type %s", ctx.getText(), tagtype));
        assert typedefEntry != null;
        ArrayList<String> visitedFields = new ArrayList<>();

        printstream.print(String.format(" \"$tag\" ::= $%d", tagValue.value));

        visitedFields.add("$tag");
        for (Map.Entry<String,SymbolTableEntry> iterator: typedefEntry.mappings.bindings.entrySet()) {
            String fieldName = iterator.getKey();

            if (ctx.exprprimary() != null) {
                if (!visitedFields.contains(tagName)) {
                    printstream.print(String.format("; \"%s\" ::= ", tagName));
                    visit(ctx.exprprimary());
                    visitedFields.add(tagName);
                }
            } else {
                int i = 0;
                for (BSVParser.MemberbindContext memberbind : ctx.memberbinds().memberbind()) {
                    String memberfieldname = String.format("%s$%s", tagName, memberbind.field.getText());
                    if (fieldName.equals(memberfieldname) && !visitedFields.contains(memberfieldname)) {
                        visitedFields.add(memberfieldname);
                        printstream.print(String.format("; \"%s\" ::= ", memberfieldname));
                        visit(memberbind.expression());
                        i++;
                    }
                }
            }
            if (!visitedFields.contains(fieldName)) {
                printstream.print(String.format("; \"%s\" ::= $0", fieldName));
            }
        }
        printstream.print(" }");
        return null;
    }
    @Override public Void visitIntliteral(BSVParser.IntliteralContext ctx) {
        printstream.print("$" + ctx.IntLiteral().getText());
        return null;
    }
    @Override public Void visitRealliteral(BSVParser.RealliteralContext ctx) {
        printstream.print("$" + ctx.RealLiteral().getText());
        return null;
    }
    @Override public Void visitReturnexpr(BSVParser.ReturnexprContext ctx) {
        printstream.print("        Ret ");
        visit(ctx.expression());
        printstream.println("");
        return null;
    }
    @Override public Void visitVarexpr(BSVParser.VarexprContext ctx) {
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
            logger.fine("var " + varName + " scope " + scope);
            if (scope.containsKey(varName)) {
                SymbolTableEntry entry = scope.lookup(varName);
                logger.fine("found binding " + varName + " " + entry.type);
                if (entry.type.name.startsWith("Reg"))
                    printstream.print("#" + varName + "_v");
                else
                    printstream.print("#" + varName);
            } else {
                printstream.print("#" + varName);
            }
        }
        return null;
    }
    @Override public Void visitArraysub(BSVParser.ArraysubContext ctx) {
        visit(ctx.array);
        printstream.print("[");
        visit(ctx.expression(0));
        if (ctx.expression(1) != null) {
            printstream.print(" : ");
            visit(ctx.expression(1));
        }
        printstream.print("]");
        return null;
    }
    @Override public Void visitLvalue(BSVParser.LvalueContext ctx) {
        if (ctx.lvalue() != null) {
            visit(ctx.lvalue());
        }
        if (ctx.index != null) {
            printstream.print("[");
            visit(ctx.index);
            printstream.print("]");
        } else if (ctx.msb != null) {
            printstream.print("[");
            visit(ctx.msb);
            printstream.print(", ");
            visit(ctx.lsb);
            printstream.print("]");
        } else if (ctx.lowerCaseIdentifier() != null) {
            if (ctx.lvalue() != null)
                printstream.print(".");
            printstream.print(ctx.lowerCaseIdentifier().getText());
        }
        return null;
    }

    @Override public Void visitCallexpr(BSVParser.CallexprContext ctx) {
        InstanceNameVisitor inv = new InstanceNameVisitor(scope);
        String methodName = inv.visit(ctx.fcn);
	if (methodName == null)
	    methodName = "FIXME$" + ctx.fcn.getText();
	assert methodName != null : "No methodName for " + ctx.fcn.getText();
        methodName = methodName.replace(".", "");
        if (methodName != null) {
            // "Call" is up where the binding is, hopefully
            printstream.print(String.format("        Call %s(", methodName));
            String sep = "";
            for (BSVParser.ExpressionContext expr: ctx.expression()) {
                printstream.print(sep);
                visit(expr);
                sep = ", ";
            }
            printstream.println("); (* method call expr *)");
        } else {
            logger.fine(String.format("How to call action function {%s}", ctx.fcn.getText()));
        }
        return null;
    }

    @Override public Void visitBeginendblock(BSVParser.BeginendblockContext ctx) {
	scope = scopes.pushScope(ctx);
	String stmtPrefix = "    ";
        for (BSVParser.StmtContext stmt: ctx.stmt()) {
            stmtEmitted = true;
            printstream.print(stmtPrefix);
            visit(stmt);
            if (stmtEmitted)
                stmtPrefix = "    with ";
        }
	scope = scopes.popScope();
	return null;
    }

    public String bsvTypeToKami(BSVType t) {
        return bsvTypeToKami(t, 0);
    }
    public String bsvTypeToKami(BSVType t, int level) {
        if (t == null)
            return "<nulltype>";
        t = t.prune();
        String kamitype = t.name;
        if (kamitype.equals("Action"))
            kamitype = "Void";
        for (BSVType p: t.params)
            kamitype += " " + bsvTypeToKami(p);
        if (level > 0)
            kamitype = String.format("&%s)", kamitype);
        return kamitype;
    }
    public String bsvTypeToKami(BSVParser.BsvtypeContext t) {
        return bsvTypeToKami(t, 0);
    }
    public String bsvTypeToKami(BSVParser.BsvtypeContext t, int level) {
        if (t == null)
            return "<nulltype>";
        if (t.typeide() != null) {
            String kamitype = t.typeide().getText();
            if (kamitype.equals("Bit") && !inModule)
                kamitype = "word";
            else if (kamitype.equals("Bool"))
                kamitype = "bool";
            else if (kamitype.equals("Action"))
                kamitype = "Void";
            for (BSVParser.BsvtypeContext p: t.bsvtype())
                kamitype += " " + bsvTypeToKami(p, 1);
            if (t.bsvtype().size() > 0)
                kamitype = String.format("(%s)", kamitype);
            return kamitype;
        } else if (t.typenat() != null) {
            return t.getText();
        } else {
            return "<functionproto>";
        }
    }
}
