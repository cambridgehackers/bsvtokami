package bsvtokami;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.io.*;
import java.util.*;
import java.util.logging.Logger;

class LetBindings implements Iterable<String>
{
    private ArrayList<String> bindings;

    LetBindings() {
	bindings = new ArrayList<>();
    }
    public void add(String binding) {
	boolean found = false;
	for (String b: bindings) {
	    if (b.equals(binding)) {
		found = true;
		break;
	    }
	}
	if (!found)
	    bindings.add(binding);
    }

    public long size() {
	return bindings.size();
    }

    public Iterator<String> iterator() {
	return bindings.iterator();
    }
}

public class GenerateIR extends BSVBaseVisitor<String>
{
    private static Logger logger = Logger.getGlobal();
    public static String newline = System.getProperty("line.separator");

    private static boolean generateWellformedDefinition = false;

    private final File ofile;
    private PrintStream printstream;
    private final StaticAnalysis scopes;
    private final BSVTypeVisitor typeVisitor;
    private SymbolTable scope;
    private String pkgName;
    private Package pkg;
    private ModuleDef moduleDef;
    private ArrayList<String> instances;
    private boolean actionContext;
    private boolean useAbstractOmega;
    private boolean stmtEmitted;
    private boolean inModule;
    // for modules and rules
    private LetBindings letBindings;
    private LetBindings methodBindings;
    private ArrayList<String> statements;
    private ArrayList<String> nextMethod;
    private ArrayList<String> modulevarbindings;
    private TreeMap<String,String> mSizeRelationshipProvisos;
    private String blockCondition;
    private static boolean traceCallm = false;
    private static int forIndex = 1;

    GenerateIR(String pkgName, File ofile, StaticAnalysis scopes) {
        this.scopes = scopes;
	this.typeVisitor = scopes.typeVisitor;
        this.pkgName = pkgName;
        this.ofile = ofile;
        pkg = new Package(pkgName);
        actionContext = false;
        inModule = false;
        blockCondition = "";
        try {
            printstream = new PrintStream(ofile);
        } catch (FileNotFoundException ex) {
            logger.severe(ex.toString());
            printstream = null;
        }
	mSizeRelationshipProvisos = new TreeMap<>();
	mSizeRelationshipProvisos.put("Add", "+");
	mSizeRelationshipProvisos.put("Mul", "*");
	mSizeRelationshipProvisos.put("Div", "/");
	mSizeRelationshipProvisos.put("Max", "max");
	mSizeRelationshipProvisos.put("Min", "min");
	mSizeRelationshipProvisos.put("Log", "log");
	nextMethod = new ArrayList<>();
    }

    void close() {
        printstream.close();
    }

    @Override public String visitImportitem(BSVParser.ImportitemContext ctx) {
	return null;
    }

    @Override
    public String visitPackagedef(BSVParser.PackagedefContext ctx) {
        logger.fine("Package " + pkgName);

        printstream.println();

        scope = scopes.pushScope(ctx);
	typeVisitor.pushScope(scope);
        if (ctx.packagedecl() != null) {
            if (!pkgName.equals(ctx.packagedecl().pkgname.getText())) {
                logger.fine("Expected " + pkgName + " found " + ctx.packagedecl().pkgname.getText());
            }
        }
        visitChildren(ctx);
        scopes.popScope();
        return null;
    }

    @Override
    public String visitPackagestmt(BSVParser.PackagestmtContext ctx) {
	statements = new ArrayList<>();
	letBindings = new LetBindings();
	visitChildren(ctx);
	if(statements.size() != 0)
            System.err.println("ERROR: Unexpected statements at " + StaticAnalysis.sourceLocation(ctx));
	//assert statements.size() == 0 : "Unexpected statements at " + StaticAnalysis.sourceLocation(ctx);
	for (String letBinding: letBindings) {
	    printstream.println(String.format("DEFINITION %s", letBinding));
	}
	return null;
    }

    @Override public String visitInterfacedecl(BSVParser.InterfacedeclContext ctx) {
	// modules are represented by a string: the name of the instance

	typeVisitor.pushScope(scope);
	BSVType interfaceType = typeVisitor.visit(ctx.typedeftype());
	typeVisitor.popScope();
	String interfaceName = interfaceType.toString();

	TreeMap<String,BSVType> freeTypeVariables = interfaceType.getFreeVariables();

	StringBuilder paramsStringBuilder = new StringBuilder();
        for (BSVType freeType: interfaceType.params) {
	    logger.fine("Ifc decl: Free type variable " + freeType + (freeType.numeric ? " nat" : " interface type"));
	    paramsStringBuilder.append(String.format(" (%s ZZIZ: %s)",
						     freeType.name,
						     (freeType.numeric ? "nat" : "Kind")));
	}
	String paramsString = paramsStringBuilder.toString();

	printstream.println(String.format("INTERFACE %s {", interfaceName));
	for (BSVParser.InterfacememberdeclContext decl: ctx.interfacememberdecl()) {
	    if (decl.methodproto() != null) {
                BSVParser.MethodprotoContext mproto = decl.methodproto();
	        assert mproto.bsvtype() != null : "Method return type required at " + StaticAnalysis.sourceLocation(mproto);
                String returntype = (mproto.bsvtype() != null) ? bsvTypeToKami(StaticAnalysis.getBsvType(mproto.bsvtype())) : "";
		printstream.print("    METHOD");
                if (returntype == "Void")
		    printstream.print("/Action");
		printstream.print(" " + mproto.name.getText());
                if (mproto.methodprotoformals() != null) {
                    printstream.print(" ( ");
                    String sep = "";
                    for (BSVParser.MethodprotoformalContext formal: mproto.methodprotoformals().methodprotoformal()) {
                        BSVType bsvtype = typeVisitor.visit(formal.bsvtype());
                        String varName = formal.name.getText();
                        printstream.print(String.format("%s%s %s", sep, bsvTypeToKami(bsvtype, 1), varName));
                        sep = ",";
                    }
                    printstream.print(" )");
                }
                if (returntype != "Void")
                    printstream.print(" " + returntype);
		printstream.println("");
	    } else {
		BSVType subinterfacetype = StaticAnalysis.getBsvType(decl.subinterfacedecl().bsvtype());
		String kamiType = bsvTypeToKami(subinterfacetype);
		assert kamiType != null;
		printstream.println(String.format("    INTERFACE %s %s",
                          kamiType, decl.subinterfacedecl().lowerCaseIdentifier().getText()));
	    }
	}
	printstream.println(String.format("}"));
	printstream.println("");
	return null;
    }

    @Override public String visitTypedefsynonym(BSVParser.TypedefsynonymContext ctx) {
        for (BSVParser.AttributeinstanceContext attrinstance: ctx.attributeinstance()) {
            for (BSVParser.AttrspecContext attr: attrinstance.attrspec()) {
                if (attr.identifier().getText().equals("nogen"))
                return null;
            }
        }
	if (ctx.bsvtype() != null) {
	    printstream.println(String.format("DEFINITION %s %s",
					      bsvTypeToKami(StaticAnalysis.getBsvType(ctx.typedeftype())),
					      bsvTypeToKami(StaticAnalysis.getBsvType(ctx.bsvtype()))
					      ));
	}
	return null;
    }

    @Override public String visitTypeclassinstance(BSVParser.TypeclassinstanceContext ctx) {
        //FIXME: overloading
        //scope = scopes.pushScope(ctx);
        //visitChildren(ctx);
        //scope = scopes.popScope();
        return null;
    }

    void declareSubstruct(ArrayList<String> members, String fieldPrefix,
                          BSVParser.SubstructContext substruct) {
        for (BSVParser.StructmemberContext member: substruct.structmember()) {
            assert member.subunion() == null;
            if (member.bsvtype() != null) {
                members.add(String.format("    \"%s$%s\" JJ1:: %s",
                                          fieldPrefix,
                                          member.lowerCaseIdentifier().getText(),
                                          bsvTypeToKami(StaticAnalysis.getBsvType(member.bsvtype()))));
            }
        }
    }

    @Override public String visitTypedefstruct(BSVParser.TypedefstructContext ctx) {
        //scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        String typeName = ctx.typedeftype().typeide().getText();
        System.err.println(String.format("BSVTOKAMI typedef struct %s\n", typeName));
        //assert ctx.typedeftype().typeformals() == null: "Typedef struct with type formals at " + StaticAnalysis.sourceLocation(ctx);
        String constructorParams = "";
        if (ctx.typedeftype().typeformals() != null) {
            StringBuilder constructorParamsBuilder = new StringBuilder();
            StringBuilder paramsBuilder = new StringBuilder();
            constructorParamsBuilder.append(" ( ");
            String sep = "";
            for (BSVParser.TypeformalContext formal: ctx.typedeftype().typeformals().typeformal()) {
                String name = formal.typeide().getText();
                //assert formal.numeric != null : "Expecting numeric type parameter at " + StaticAnalysis.sourceLocation(formal);
                constructorParamsBuilder.append(String.format("%s%s", sep, name));
                paramsBuilder.append(String.format(" %s", name));
                sep = ", ";
            }
            constructorParamsBuilder.append(" ) ");
            constructorParams = constructorParamsBuilder.toString();
        }

        printstream.println(String.format("STRUCT %s%s {", typeName, constructorParams));
        ArrayList<String> members = new ArrayList<>();
	SymbolTableEntry structTypeEntry = scope.lookupType(typeName);
	assert structTypeEntry != null : "No entry for type name " + typeName;;
        for (Map.Entry<String,SymbolTableEntry> iterator: structTypeEntry.mappings.bindings.entrySet()) {
	    String fieldName = iterator.getKey();
	    // emit them in the order they are stored in the mapping
	    for (BSVParser.StructmemberContext member: ctx.structmember()) {
		String memberName = member.lowerCaseIdentifier().getText();
		if (!memberName.equals(fieldName))
		    continue;
		assert member.subunion() == null;
		if (member.bsvtype() != null) {
		    members.add(String.format("    %s %s", //jca
					      bsvTypeToKami(StaticAnalysis.getBsvType(member.bsvtype())),
					      memberName));
		} else {
		}
	    }
	}
        printstream.print(String.join(";\n", members));
        printstream.println(";\n}");

        //scope = scopes.popScope();
        inModule = wasInModule;
        return null;
    }

    @Override public String visitTypedefenum(BSVParser.TypedefenumContext ctx) {
        //scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        String typeName = ctx.upperCaseIdentifier().getText();
        System.err.println(String.format("BSVTOKAMI typedef enum %s\n", typeName));

        String typedefname = ctx.upperCaseIdentifier().getText();

	// go through them all and collect names and values
	// then bit width from max value
	// then generate statements

	class TagValue {
	    String tag;
	    long value;
	    TagValue(String tag, long value) {
		this.tag = tag;
		this.value = value;
	    }
	};
	ArrayList<TagValue> tagsAndValues = new ArrayList<>();
	long maxValue = 0;
	long tagValue = 0;
	long tagFrom = 0;
	for (BSVParser.TypedefenumelementContext elt: ctx.typedefenumelement()) {
            String basetagname = elt.upperCaseIdentifier().getText();
            long tagCount = 1;
            boolean numbered = false;

            if (elt.tagval != null) {
		IntValue intValue = new IntValue(elt.tagval.getText());
                tagValue = intValue.value;
            }

            if (elt.from != null) {
                numbered = true;
		IntValue intValue = new IntValue(elt.from.getText());
                tagCount = intValue.value;
                if (elt.to != null) {
                    tagFrom = tagCount;
		    intValue = new IntValue(elt.to.getText());
                    tagCount = intValue.value - tagFrom + 1;
                }
            }

            System.err.println(String.format("enum %s %s%s%s%s tagCount %d tagFrom %d",
                                             basetagname,
					     ((elt.from != null) ? "from " : ""),
                                             ((elt.from != null) ? elt.from.getText() : ""),
					     ((elt.to != null) ? " to " : ""),
                                             ((elt.to != null) ? elt.to.getText() : ""),
					     tagCount,
					     tagFrom));
            for (int i = 0; i < tagCount; i++) {
                String tagname = basetagname;
                if (numbered) {
                    tagname = String.format("%s%d", basetagname, tagFrom + i);
                }
                SymbolTableEntry entry = scope.lookup(tagname);
                assert entry != null : String.format("No entry for %s at %s", tagname, StaticAnalysis.sourceLocation(ctx));
                assert entry.value != null;
                IntValue entryValue = (IntValue)entry.value;
                assert entryValue != null;
		maxValue = java.lang.Math.max(maxValue, tagFrom + i);
		System.err.println("tag entry " + tagname + "    maxValue " + maxValue);
		tagsAndValues.add(new TagValue(tagname, tagFrom + i //entryValue.value
					       ));
            }
	    tagFrom += tagCount;
        }
	System.err.println(String.format("enum %s maxValue %d", typeName, maxValue));
	maxValue += 1;
	int tagSize = (int)java.lang.Math.ceil(java.lang.Math.log(maxValue) / java.lang.Math.log(2.0));
	// emit type declaration
        printstream.println(String.format("4STRUCT %s { \"$tag\" JJ3:: (Bit %d) }).", typeName, tagSize));

	for (TagValue pair: tagsAndValues) {
	    if (pair.value < 128)
		printstream.println(String.format("5STRUCT  %s {ty} : %s @# ty := { \"$tag\" ::= $$(%s) }",
						  pair.tag, typeName, intToWord(tagSize, pair.value)));

	}


        //scope = scopes.popScope();
        inModule = wasInModule;
        return null;
    }
    @Override public String visitTypedeftaggedunion(BSVParser.TypedeftaggedunionContext ctx) {
        //scope = scopes.pushScope(ctx);
        boolean wasInModule = inModule;
        inModule = true;

        String typeName = ctx.typedeftype().typeide().getText();
        String constructorParams = "";
        String params = "";
        if (ctx.typedeftype().typeformals() != null) {
            StringBuilder constructorParamsBuilder = new StringBuilder();
            StringBuilder paramsBuilder = new StringBuilder();
            for (BSVParser.TypeformalContext formal: ctx.typedeftype().typeformals().typeformal()) {
                String name = formal.typeide().getText();
                if(formal.numeric == null) {
                    System.err.println("ERROR: Expecting numeric type parameter at " + StaticAnalysis.sourceLocation(formal));
                    return "ERRORTAGGEDUNION";
                }
                assert formal.numeric != null : "Expecting numeric type parameter at " + StaticAnalysis.sourceLocation(formal);
                constructorParamsBuilder.append(String.format(" (%s : nat)", name));
                paramsBuilder.append(String.format(" %s", name));
            }

            constructorParams = constructorParamsBuilder.toString();
            params = paramsBuilder.toString();
        }

        System.err.println(String.format("BSVTOKAMI typedef tagged union %s\n", typeName));

        printstream.println(String.format("6STRUCT %s%s {", typeName, constructorParams));
        ArrayList<String> members = new ArrayList<>();
        members.add(String.format("    \"$tag\" :: (Bit 8)"));
	SymbolTableEntry typeEntry = scope.lookupType(typeName);
	assert typeEntry != null;
        for (Map.Entry<String,SymbolTableEntry> iterator: typeEntry.mappings.bindings.entrySet()) {
	    String fieldName = iterator.getKey();

	    for (BSVParser.UnionmemberContext member: ctx.unionmember()) {
		String memberName = member.upperCaseIdentifier().getText();
		if (!memberName.equals(fieldName))
		    continue;
		assert member.subunion() == null;
		if (member.bsvtype() != null) {
		    members.add(String.format("    \"%s\" JJ5:: %s",
					      memberName,
					      bsvTypeToKami(StaticAnalysis.getBsvType(member.bsvtype()))));
		} else if (member.substruct() != null) {
		    declareSubstruct(members, memberName, member.substruct());
		} else {
		}
	    }
	}
        printstream.print(String.join(";\n", members));
        printstream.println("}).");
        //scope = scopes.popScope();
        inModule = wasInModule;
        return null;
    }

    @Override public String visitModuledef(BSVParser.ModuledefContext ctx) {
	LetBindings parentMethodBindings = methodBindings;
	LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;
	methodBindings = new LetBindings();
	letBindings = new LetBindings();
	statements = new ArrayList<>();
	modulevarbindings = new ArrayList<>();

        for (BSVParser.AttributeinstanceContext attrinstance: ctx.attributeinstance()) {
            for (BSVParser.AttrspecContext attr: attrinstance.attrspec()) {
                if (attr.identifier().getText().equals("nogen"))
                return null;
            }
        }
        instances = new ArrayList<>();
        scope = scopes.pushScope(ctx);
	typeVisitor.pushScope(scope);

        BSVParser.ModuleprotoContext moduleproto = ctx.moduleproto();
        String moduleName = moduleproto.name.getText();
	moduleName = (moduleName.startsWith("mk") ? moduleName.substring(2) : moduleName);
	String interfaceName = moduleName;
	BSVType moduleType = typeVisitor.visit(ctx.moduleproto());
	TreeMap<String,BSVType> freeTypeVariables = moduleType.getFreeVariables();
	logger.fine(String.format("module %s type %s free vars %d",
				  moduleName, moduleType, freeTypeVariables.size()));
	BSVType interfaceType;
	if (ctx.moduleproto().moduleinterface != null) {
	    // FIXME
	    interfaceType = typeVisitor.visit(ctx.moduleproto().moduleinterface);
	    assert interfaceType != null;
	} else {
	    // FIXME also
	    interfaceType = typeVisitor.visit(ctx.moduleproto().methodprotoformals().methodprotoformal(0));
	    assert interfaceType != null;
	}
        interfaceType = typeVisitor.dereferenceTypedef(interfaceType);
	interfaceName = interfaceType.name;
        String iname = interfaceType.toString();
        if (!iname.equals("Empty")) {
	    ArrayList<String> convertedParams = new ArrayList<>();
            /* prepend module params */
            if (moduleproto.methodprotoformals() != null) {
                for (BSVParser.MethodprotoformalContext formal : moduleproto.methodprotoformals().methodprotoformal()) {
                    if (formal.name != null)
                        convertedParams.add(formal.name.getText());
                }
            }
            /* now add interface params */
	    for (BSVType p: interfaceType.params)
	        convertedParams.add(bsvTypeToKami(p, 1));
	    if (convertedParams.size() > 0)
	        moduleName = String.format("%s(%s)", moduleName, String.join(",", convertedParams));
        }

	moduleDef = new ModuleDef(moduleName);
        pkg.addStatement(moduleDef);
        InstanceNameVisitor inv = new InstanceNameVisitor(scopes);
        inv.visit(ctx);
	if (inv.methodsUsed.size() > 0) {
	    System.err.println(String.format("Module %s instances visited %s",
					     moduleName,
					     String.join(", ", inv.methodsUsed.keySet())));
	    for (Map.Entry<String,InstanceEntry> iterator: inv.methodsUsed.entrySet()) {
		InstanceEntry ie = iterator.getValue();
		System.err.print(String.format("    %s: <%s'%s>", ie.instanceName, ie.interfaceName, ie.methodName));
	    }
	}

        logger.fine("module " + moduleName);
	printstream.println("MODULE " + moduleName + " {");
        if (!iname.equals("Empty"))
	    printstream.println("    INTERFACE " + interfaceType.toString());
        for (Map.Entry<String,BSVType> entry: freeTypeVariables.entrySet()) {
	    BSVType freeType = entry.getValue();
	    boolean isNumeric = freeType.numeric;
	    // FIXME: heuristic
	    if (freeType.name.startsWith("Num") || freeType.name.endsWith("sz") || freeType.name.endsWith("Sz") || freeType.name.equals("xlen"))
		isNumeric = true;
	    logger.fine("Module def: Free type variable " + freeType + (isNumeric ? " numeric" : " interface type"));
	}
        boolean wasInModule = inModule;
        inModule = true;

	boolean hasProvisos = moduleproto.provisos() != null;
	useAbstractOmega = false; // does not seem to work with sifive kami: hasProvisos;
	if (hasProvisos) {
	    for (BSVParser.ProvisoContext proviso: moduleproto.provisos().proviso()) {
		// emit Variable declaration for free variable in proviso
		for (BSVParser.BsvtypeContext bsvtype: proviso.bsvtype()) {
		    String typeVariable = bsvtype.getText();
		    if (typeVariable.matches("[0-9]+"))
			continue;
		    if (!freeTypeVariables.containsKey(typeVariable)) {
			freeTypeVariables.put(typeVariable, typeVisitor.visit(bsvtype));
		    }
		}
		String constraint = visit(proviso);
		if (constraint != null)
		    printstream.println(String.format("    %s", constraint));
		// emit hypothesis for proviso
	    }
	}
        String stmtPrefix = "";
        for (BSVParser.ModulestmtContext modulestmt: ctx.modulestmt()) {
            visit(modulestmt);
        }
	if (letBindings.size() > 0) {
	    printstream.print(stmtPrefix);
	    printstream.println("(* let bindings *)");
	    for (String letBinding: letBindings) {
		printstream.print(stmtPrefix);
		printstream.println(String.format("%s%s.",
						  (letBinding.startsWith("Definition") ? "" : "LET "),
						  letBinding));
	    }
	}

	if (statements.size() > 0) {
	    for (String statement: statements) {
		printstream.print(stmtPrefix);
		printstream.println(String.format("    %s", statement));
	    }
	}

	SymbolTableEntry interfaceEntry = scope.lookupType(interfaceName);
	if(interfaceEntry == null) {
            System.err.println("ERROR: No symbol table entry for interface " + interfaceName + " at location " + StaticAnalysis.sourceLocation(ctx));
            return null;
        }
	assert interfaceEntry != null: "No symbol table entry for interface " + interfaceName + " at location " + StaticAnalysis.sourceLocation(ctx);
        assert interfaceEntry.mappings != null: "No interface mappings for " + interfaceName + " at location " + StaticAnalysis.sourceLocation(ctx);

        printstream.println("}");
	typeVisitor.popScope();
        scope = scopes.popScope();
        moduleDef = null;
        logger.fine("endmodule : " + moduleName);
        inModule = wasInModule;

	methodBindings = parentMethodBindings;
	letBindings = parentLetBindings;
	statements  = parentStatements;
        return null;
    }

    BSVParser.CallexprContext getCall(ParserRuleContext ctx) {
        return new CallVisitor().visit(ctx);
    }

    @Override public String visitVarBinding(BSVParser.VarBindingContext ctx) {
	assert statements != null : "Visiting var binding but not collecting statements at " + StaticAnalysis.sourceLocation(ctx);
	typeVisitor.pushScope(scope);

	BSVType t = typeVisitor.visit(ctx.t);

        for (BSVParser.VarinitContext varinit: ctx.varinit()) {
	    StringBuilder statement = new StringBuilder();
            String varName = varinit.var.getText();
            assert scope != null : "No scope to evaluate var binding " + ctx.getText();
            SymbolTableEntry varEntry = scope.lookup(varName);
            BSVParser.ExpressionContext rhs = varinit.rhs;
	    assert varEntry != null : "No var entry for " + varName + " at " + StaticAnalysis.sourceLocation(ctx);
	    BSVType varType = varEntry.type;
	    if (varType.name.equals("t"))
		System.err.println(String.format("looking for tvar %s prune %s",
						 varType.name, varType.prune()));
            if (rhs != null) {
		BSVType rhsType = typeVisitor.visit(rhs);
		try {
		    rhsType.unify(varType);
		} catch (InferenceError e) {
		    logger.fine(e.toString());
		    System.err.println(e.toString() + " at " + StaticAnalysis.sourceLocation(ctx));
		}
                BSVParser.CallexprContext call = getCall(rhs);
                if (call != null) {
		    String functionName = "";
		    if (call != null)
			functionName = call.fcn.getText();

		    System.err.println(String.format("var binding functionName=%s %s at %s",
						     functionName,
						     (actionContext ? "action context" : "other context"),
						     StaticAnalysis.sourceLocation(ctx)));

		    List<BSVParser.ExpressionContext> args = call.expression();

		    if (functionName.equals("fromInteger")) {
			if (actionContext) {
			    statement.append(String.format("LET %1$s : %2$s <- $%3$s",
						       varName,
						       bsvTypeToKami(t, 1),
						       visit(args.get(0))));
			} else {
			    letBindings.add(String.format("%s %s", varName, visit(args.get(0))));
			}
		    } else if (functionName.equals("truncate")) {
			BSVType arg0Type = typeVisitor.visit(args.get(0));
			String lsbWidth = bsvTypeSize(varType, varinit.var);
			String exprWidth = bsvTypeSize(arg0Type, args.get(0));
			String msbWidth = String.format("(%s - %s)", exprWidth, lsbWidth);
			statement.append(String.format((useAbstractOmega
						       ? "LET %1$s : %2$s <- UniBit (Trunc %3$s %4$s) (castBits _ %6$s (%3$s + %4$s) _ %5$s)"
							: "LET %1$s : %2$s <- UniBit (Trunc %3$s %4$s) %5$s"),
						       varName,
						       bsvTypeToKami(t, 1),
						       lsbWidth,
						       msbWidth,
						       visit(args.get(0)),
						       exprWidth));
		    } else if (functionName.equals("truncateLSB")) {
			BSVType arg0Type = typeVisitor.visit(args.get(0));
			String lsbWidth = bsvTypeSize(varType, varinit.var);
			String exprWidth = bsvTypeSize(arg0Type, args.get(0));
			String msbWidth = String.format("(%s - %s)", exprWidth, lsbWidth);
			statement.append(String.format((useAbstractOmega
							? "LET %1$s : %2$s <-  UniBit (TruncLsb %3$s %4$s) (castBits _ %6$s %6$s _ %5$s)"
							: "LET %1$s : %2$s <-  UniBit (TruncLsb %3$s %4$s) %5$s"),
						       varName,
						       bsvTypeToKami(t, 1),
						       msbWidth,
						       lsbWidth,
						       visit(args.get(0)),
						       exprWidth));
		    } else if (functionName.equals("arithmeticShift")) {
			String leftValue = visit(args.get(0));
			String rightValue = visit(args.get(1));
			BSVType leftType = typeVisitor.visit(args.get(0));
			BSVType rightType = typeVisitor.visit(args.get(1));
			String leftWidth = bsvTypeSize(leftType, args.get(0));
			String rightWidth = bsvTypeSize(rightType, args.get(1));
			String kamiOp = "Sra";
			statement.append(String.format("LET %1$s : %2$s <- (BinBit (%7$s %3$s %4$s) %5$s %6$s)",
						       varName,
						       bsvTypeToKami(varType, 1),
						       leftWidth, rightWidth,
						       leftValue, rightValue,
						       kamiOp));
		    } else if (functionName.equals("signExtend") || functionName.equals("zeroExtend") || functionName.equals("extend")) {
			boolean wasActionContext = actionContext;
			actionContext = true;

			BSVType arg0Type = typeVisitor.visit(args.get(0));
			if (functionName.equals("extend"))
			    functionName = (arg0Type.name.startsWith("Int")) ? "signExtend" : "zeroExtend";
			System.err.println(String.format("extending var %1$s to type %2$s from %3$s", varName, varType, arg0Type));
			String op = (functionName.equals("signExtend")) ? "SignExtendTrunc" : "ZeroExtendTrunc";
			String arg0Width = bsvTypeSize(arg0Type, args.get(0));
			String varWidth = bsvTypeSize(varType, varinit.var);
			statement.append(String.format((useAbstractOmega
							? "LET %1$s : %2$s <-  SignExtend (%4$s - %3$s) (castBits _ %3$s %3$s _ %5$s)"
							: "LET %1$s : %2$s <-  SignExtend (%4$s - %3$s) %5$s"),
						       varName,
						       bsvTypeToKami(varType, 1),
						       arg0Width,
						       varWidth,
						       visit(args.get(0))));
			actionContext = wasActionContext;
		    } else if (functionName.equals("pack") || functionName.equals("unpack")) {
			BSVType arg0Type = typeVisitor.visit(args.get(0));
			statement.append(String.format("LET %1$s : %2$s <-  %3$s %5$s %4$s",
						       varName,
						       bsvTypeToKami(varType, 1),
						       functionName,
						       visit(args.get(0)),
						       (functionName.equals("unpack")
							? varType
							: "")
						       ));
		    } else if (functionName.startsWith("tuple")) {
			BSVType arg0Type = typeVisitor.visit(args.get(0));
			StringBuilder struct = new StringBuilder();
			for (int i = 0; i < args.size(); i++) {
			    if (i != 0)
				struct.append(" ; ");
			    struct.append(String.format("\"tpl_%d\" ::= (%s)", i + 1, visit(args.get(i))));
			}
			statement.append(String.format("LET %1$s : %2$s <- STRUCT { %3$s }",
						       varName,
						       bsvTypeToKami(varType, 1),
						       struct.toString()));
		    } else if (functionName.startsWith("tpl_")) {
			BSVType arg0Type = typeVisitor.visit(args.get(0));
			statement.append(String.format("LET %1$s : %2$s <-  %3$s . tpl_%4$s",
						       varName,
						       bsvTypeToKami(varType, 1),
						       visit(args.get(0)),
						       functionName.substring(4)));
		    } else {
			System.err.println(String.format("Call varbinding %s fcn %s", varName, functionName));
			boolean wasActionContext = actionContext;
			actionContext = true;
			statement.append(String.format("LET %s : %s = %s ", bsvTypeToKami(t), varName, translateCall(call)));
			actionContext = wasActionContext;
		    }
                } else {
                    if (inModule) {
                        statement.append(String.format("        LET %s %s : %s = ", bsvTypeToKami(t), blockCondition, varName));
			boolean wasActionContext = actionContext;
			actionContext = true;
                        statement.append(visit(rhs));
			actionContext = wasActionContext;
                    } else {
                        letBindings.add(String.format("%s %s", varName, visit(rhs)));
                        statement.append("(* varbinding in action context *)");
                        varEntry.isConstT = true;
                    }
                }
            } else {
                System.err.println("No rhs for " + ctx.getText() + " at " + StaticAnalysis.sourceLocation(ctx));
                statement.append(String.format("        LET %s %s : %s", bsvTypeToKami(t), blockCondition, varName));
            }
            if (actionContext) {
                statements.add(statement.toString());
            } else if (inModule) {
                modulevarbindings.add(statement.toString());
            } else {
                // already added to letBindings
            }
        }
	typeVisitor.popScope();
	return null;
    }

    @Override public String visitLetBinding(BSVParser.LetBindingContext ctx) {
        BSVParser.ExpressionContext rhs = ctx.rhs;
        BSVParser.CallexprContext call = getCall(rhs);
        assert ctx.lowerCaseIdentifier().size() == 1;
	StringBuilder statement = new StringBuilder();
	statement.append("        LET ");
        for (BSVParser.LowerCaseIdentifierContext ident: ctx.lowerCaseIdentifier()) {
            String varName = ident.getText();
            SymbolTableEntry entry = scope.lookup(varName);
            assert entry != null : String.format("No entry for %s at %s",
                                                 varName, StaticAnalysis.sourceLocation(ctx));
            statement.append(String.format("%s %s : %s", bsvTypeToKami(entry.type), blockCondition, varName));
        }

        if (ctx.op != null) {
            statement.append(String.format(" %s ", (call != null) ? "=" : ctx.op.getText()));
	    statement.append(visit(ctx.rhs));
	    statement.append(" ");
	}
        statements.add(statement.toString());
	return null;
    }
    @Override public String visitActionBinding(BSVParser.ActionBindingContext ctx) {
	typeVisitor.pushScope(scope);

        String varName = ctx.var.getText();
        BSVParser.ExpressionContext rhs = ctx.rhs;
        SymbolTableEntry entry = scope.lookup(varName);
        assert entry != null: "Null var name in " + ctx.getText();
        BSVType bsvtype = entry.type;
        String typeName = bsvtype.name;
        InstanceNameVisitor inv = new InstanceNameVisitor(scopes);
	inv.pushScope(scope);
        String calleeInstanceName = inv.visit(ctx.rhs);
        //if (calleeInstanceName != null && actionContext)
            //calleeInstanceName = calleeInstanceName.replace(".", "");

	StringBuilder statement = new StringBuilder();

        if (false && !typeName.equals("Bit")) {
            BSVType paramtype = bsvtype.params.get(0);
	    methodBindings.add(String.format("%s STRING", varName, varName));
            statement.append("FIELD " + bsvTypeToKami(paramtype) + varName + " <- ");
            BSVParser.CallexprContext call = getCall(ctx.rhs);
	    if (call != null)
		logger.fine("Register " + call.getText() + " fcn " + ((call.fcn != null) ? call.fcn.getText() : "")
			    + " at " + StaticAnalysis.sourceLocation(call));

            if (call != null && call.fcn != null && call.fcn.getText().equals("mkReg")) {
		logger.fine("mkReg " + call.expression().get(0).getText());
                statement.append(visit(call.expression().get(0)));
	    } else if (call != null && call.fcn != null && call.fcn.getText().equals("mkRegU")) {
		logger.fine("mkRegU");
                statement.append("Default");
            } else {
                statement.append(visit(ctx.rhs));
            }

        } else if (calleeInstanceName != null && actionContext) {
            BSVParser.CallexprContext call = getCall(ctx.rhs);
	    if(call == null || call.fcn == null) {
                System.err.println("ERROR: Something wrong with action context " + ctx.rhs.getText() + " at " + StaticAnalysis.sourceLocation(ctx.rhs));
                return null;
            }
	    assert call != null && call.fcn != null: "Something wrong with action context " + ctx.rhs.getText() + " at " + StaticAnalysis.sourceLocation(ctx.rhs);

	    statement.append(String.format("        CALL/Action %s : %s(", blockCondition, calleeInstanceName));
            String sep = "";
	    for (BSVParser.ExpressionContext arg: call.expression()) {
		BSVType argType = typeVisitor.visit(arg);
		statement.append(String.format("%s %s", sep, visit(arg)));
                sep = ", ";
	    }
	    statement.append(")");

        } else if (!actionContext) {
            BSVParser.CallexprContext call = getCall(ctx.rhs);
	    if(call == null || call.fcn == null) {
                System.err.println( "ERROR: Something wrong with " + ctx.rhs.getText() + " at " + StaticAnalysis.sourceLocation(ctx.rhs));
                return null;
            }
	    assert call != null && call.fcn != null: "Something wrong with " + ctx.rhs.getText() + " at " + StaticAnalysis.sourceLocation(ctx.rhs);
	    String fcnName = call.fcn.getText();
	    SymbolTableEntry fcnEntry = scope.lookup(fcnName);
	    BSVType moduleType = fcnEntry.type.fresh();
	    BSVType interfaceType = getModuleType(moduleType);
	    try {
		interfaceType.unify(bsvtype);
	    } catch (InferenceError e) {
		logger.fine(e.toString());
	    }
            if (interfaceType.name.equals("Reg"))
                interfaceType = interfaceType.params.get(0).instance;
	    System.err.println(String.format("fcnName %s moduleType %s interfaceType %s",
					     fcnName, moduleType, interfaceType));
	    String interfaceName = interfaceType.toString();
	    StringBuilder typeParameters = new StringBuilder();
	    StringBuilder params = new StringBuilder();
	    BSVType t = moduleType;
	    int argNum = 0;
	    for (BSVParser.ExpressionContext arg: call.expression()) {
		BSVType argType = typeVisitor.visit(arg);
		System.err.println(String.format("    arg %s type %s name %s", arg.getText(), argType, t.name));
		//jca assert t.name.equals("Function");
		try {
		    t.params.get(0).unify(argType);
		} catch (InferenceError e) {
		    logger.fine(e.toString());
		}
if (t.params.size() < 2) { //jca
System.err.println("paramsizeless2 " + t.params.size());
break;
}
		t = t.params.get(1);
	    }
	    if (!t.name.equals("Module")) {
                System.err.println("ERROR: NOTMOD " +  String.format("Expected Module but got %s in type %s at %s",
							   t.name, t, StaticAnalysis.sourceLocation(call)));
                return null;
            }
	    assert t.name.equals("Module") : String.format("Expected Module but got %s in type %s at %s",
							   t.name, t, StaticAnalysis.sourceLocation(call));
	    List<BSVType> moduleFreeTypeVars = interfaceType.getInstanceVariables();

	    for (BSVParser.ExpressionContext arg: call.expression()) {
		params.append(" ");
		params.append(String.format("(%s)%%bk", visit(call.expression(argNum++))));
	    }

	    boolean wasActionContext = actionContext;
	    actionContext = true;
	    for (BSVType ft: moduleFreeTypeVars) {
		typeParameters.append(" (");
		typeParameters.append(bsvTypeToKami(ft));
		typeParameters.append(")");
	    }
	    actionContext = wasActionContext;

	    System.err.println(String.format("Module instantiation fcn %s type %s interface %s at %s",
					     fcnName, fcnEntry.type, interfaceType,
					     StaticAnalysis.sourceLocation(ctx.rhs)));
	    if (moduleFreeTypeVars.size() != 0 || true)
		System.err.println("   freeTypeVars: " + typeParameters.toString());
            methodBindings.add(String.format("(* action binding *) %s := %s%s %s%s",
					     varName, fcnName, typeParameters.toString(), varName,
					     params.toString()));
            statement.append(String.format("FIELD %s %s", interfaceName, varName));

            String instanceName = String.format("%s", varName); //FIXME concat methodName
            entry.instanceName = instanceName;

            //instances.add(String.format("%s(\"%s\")", call.fcn.getText(), instanceName));
        } else {
            statement.append(String.format("        Call %s (* here *) <- %s(", varName, calleeInstanceName));
            logger.fine("generic call " + ctx.rhs.getRuleIndex() + " " + ctx.rhs.getText());
            BSVParser.CallexprContext call = getCall(ctx.rhs);
            String sep = "";
            for (BSVParser.ExpressionContext expr: call.expression()) {
                statement.append(sep + "(" + visit(expr) + ")");
                sep = ", ";
            }
            statement.append(")");
        }
	statements.add(statement.toString());
	typeVisitor.popScope();
	return null;
    }

    @Override public String visitRuledef(BSVParser.RuledefContext ruledef) {
	LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;
	letBindings = new LetBindings();
	statements = new ArrayList<>();

        boolean outerContext = actionContext;
        actionContext = true;
        scope = scopes.pushScope(ruledef);
        String ruleName = ruledef.name.getText();
        RuleDef ruleDef = new RuleDef(ruleName);
        BSVParser.RulecondContext rulecond = ruledef.rulecond();
        moduleDef.addRule(ruleDef);

        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        if (rulecond != null)
	    regReadVisitor.visit(rulecond);
        for (BSVParser.StmtContext stmt: ruledef.rulebody().stmt()) {
            regReadVisitor.visit(stmt);
        }

	StringBuilder statement = new StringBuilder();
        statement.append("METHOD/Rule/Action " + ruleName);
        if (rulecond != null) {
            String rulecondValue = visit(rulecond);
            statement.append(" if (" + rulecondValue + ")");
        }
        statement.append(" {\n");

        if (rulecond != null) {
	    BSVType rulecondtype = typeVisitor.visit(rulecond);
	    try {
		rulecondtype.unify(new BSVType("Bool"));
	    } catch (InferenceError e) {
		logger.fine(e.toString());
		System.err.println(e.toString() + " at " + StaticAnalysis.sourceLocation(rulecond));
	    }
	    if (modulevarbindings.size() > 0) {
                for (String s: modulevarbindings) {
                    statement.append("QQ99       " + s + newline);
                }
	    }
            if (statements.size() > 0) {
                for (String s: statements) {
                    statement.append("    " + s + newline);
                }
                statements.clear();
            }
        }

	// now visit the body statements
        for (BSVParser.StmtContext stmt: ruledef.rulebody().stmt()) {
            visit(stmt);
        }
	//
	if (letBindings.size() > 0) {
	    statement.append("       ");
	    for (String ruleLetBinding: letBindings) {
		statement.append(String.format("       let %s in\n", ruleLetBinding));
	    }
	}
	if (statements.size() > 0) {
	    for (String ruleStatement: statements) {
		statement.append("       " + ruleStatement + newline);
	    }
	}
        statement.append("        }");
        scope = scopes.popScope();
        actionContext = outerContext;

	letBindings = parentLetBindings;
	statements  = parentStatements;
	statements.add(statement.toString());

        return null;
    }

    @Override public String visitFunctiondef(BSVParser.FunctiondefContext ctx) {
        LetBindings parentMethodBindings = methodBindings;
        LetBindings parentLetBindings = letBindings;
        ArrayList<String> parentStatements = statements;
        methodBindings = new LetBindings();
        letBindings = new LetBindings();
        statements = new ArrayList<>();
        modulevarbindings = new ArrayList<>();
        scope = scopes.pushScope(ctx);

        for (BSVParser.AttributeinstanceContext attrinstance: ctx.attributeinstance()) {
            for (BSVParser.AttrspecContext attr: attrinstance.attrspec()) {
                if (attr.identifier().getText().equals("nogen"))
                return null;
            }
        }

        InstanceNameVisitor inv = new InstanceNameVisitor(scopes);
        inv.visit(ctx);

        BSVParser.FunctionprotoContext functionproto = ctx.functionproto();
	String functionName = functionproto.name.getText();
	BSVType functionType = typeVisitor.visit(functionproto);
	TreeMap<String,BSVType> freeTypeVariables = functionType.getFreeVariables();
	System.err.println(String.format("Translating function def %s type %s free type vars (%s)",
					 functionName, functionType,
					 String.join(" ", freeTypeVariables.keySet())));

	//printstream.println(String.format("(* interface for module wrapper for %1$s *)", functionName));
	//printstream.println(String.format("Record Interface'%1$s := {", functionName));
	//printstream.println(String.format("    Interface'%1$s'mod: Mod;", functionName));
	//printstream.println(String.format("    Interface'%1$s'%1$s: string;", functionName));
	//printstream.println(String.format("}."));
	//printstream.println(String.format(""));
	//printstream.println(String.format("MODULE %s {", functionName));

        for (Map.Entry<String,BSVType> entry: freeTypeVariables.entrySet()) {
            BSVType freeType = entry.getValue();
            boolean isNumeric = freeType.numeric;
            // FIXME: heuristic
            if (freeType.name.endsWith("sz") || freeType.name.endsWith("Sz") || freeType.name.equals("xlen"))
                isNumeric = true;
            logger.fine("Function def: Free type variable " + freeType + (isNumeric ? " numeric" : " interface type"));
            //printstream.println(String.format("    %s %s",
                       //(isNumeric ? "nat" : "Kind"), entry.getKey()));
        }

	boolean wasActionContext = actionContext;
	actionContext = true;
	StringBuilder functionBody = new StringBuilder();

        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
        if (ctx.expression() != null) {
            //printstream.print("    ");
            regReadVisitor.visit(ctx.expression());

        if (ctx.expression() != null)
            functionBody.append(visit(ctx.expression()));
        } else {
            for (BSVParser.StmtContext stmt: ctx.stmt())
                regReadVisitor.visit(stmt);
            for (BSVParser.StmtContext stmt: ctx.stmt())
                visit(stmt);

	    if (letBindings.size() > 0)
		System.err.println("Unexpected let bindings in function def at " + StaticAnalysis.sourceLocation(ctx) + "\n" + String.join("\n    ", letBindings));
	    if (statements.size() > 0) {
		functionBody.append("        ");
		functionBody.append(String.join(" ;\n        ", statements));
	    }
        }

	actionContext = wasActionContext;

	//FIXME letBindings go here

        for (Map.Entry<String,InstanceEntry> iter: inv.methodsUsed.entrySet()) {
            InstanceEntry methodEntry = iter.getValue();
            String instanceName = methodEntry.instanceName;
	    String method = methodEntry.methodName;
	    BSVType methodType = methodEntry.methodType;
	    System.err.println(String.format("INV: function def instance %s method %s : %s",
					     instanceName, method, methodType));
	    if (methodType.name.equals("Function"))  {
		assert methodType.params.size() == 2: "Unhandled method " + method + " has type " + methodType + " from interface " + methodEntry.interfaceName;
		BSVType argType = methodType.params.get(0);
		BSVType returnType = methodType.params.get(1);
		String methodInterfaceName = methodEntry.interfaceName;
		//printstream.println(String.format("    LET %1$s%2$s : string := (%3$s'%2$s %1$s).",
						  //instanceName, method, methodInterfaceName));
	    } else {
		//printstream.println(String.format("(* FIXME: interface %s subinterface %s *)", methodEntry.interfaceName, method));
	    }
        }
	//for (String letBinding: letBindings) {
	    //printstream.println(String.format("       LET %s.", letBinding));
	//}
	//for (String methodBinding: methodBindings) {
	    //printstream.println(String.format("       12Definition %s.\n", methodBinding));
	//}

	boolean hasProvisos = functionproto.provisos() != null;
	useAbstractOmega = hasProvisos;
/*
	printstream.println(String.format("    13Definition Mod'%s: Mod%s",
					  functionName,
					  (useAbstractOmega ? "." : " :=")
					  ));
	printstream.println(String.format("        %s (BKMODULE {",
					  (useAbstractOmega ? "refine" : "")));
	//FIXME module instantiations go here
	int numArguments = (functionproto.methodprotoformals() != null)
	    ? functionproto.methodprotoformals().methodprotoformal().size()
	    : 0;
	printstream.print(String.format("    METHOD %s ", functionName));

        if (functionproto.methodprotoformals() != null) {
            String sep = "";
            printstream.print("( ");
            for (BSVParser.MethodprotoformalContext formal: functionproto.methodprotoformals().methodprotoformal()) {
                BSVType bsvType = StaticAnalysis.getBsvType(formal);
                String formalName = StaticAnalysis.getFormalName(formal);
                printstream.print(String.format("%s%s %s", sep, bsvTypeToKami(bsvType, 1), formalName));
                sep = ", ";
            }
            printstream.print(" ) ");
        }
        String returntype = (functionproto.bsvtype() != null) ? bsvTypeToKami(StaticAnalysis.getBsvType(functionproto.bsvtype())) : "";
        printstream.print(String.format(" %s = ", returntype));
	printstream.println(" {");
	printstream.println(functionBody.toString());
        printstream.println(String.format("    }"));
        printstream.println(String.format("    14Definition %1$s := Build_Interface'%1$s Mod'%1$s %1$s.", functionName));
	printstream.println(String.format("}")); // functionName));
	printstream.println("");
        printstream.println(String.format("15Definition function'%1$s := module'%1$s.%1$s.", functionName));
	printstream.println("");
	printstream.println("");
*/

	actionContext = wasActionContext;
	methodBindings = parentMethodBindings;
        letBindings = parentLetBindings;
        statements  = parentStatements;
        scope = scopes.popScope();
        return null;
    }

    @Override public String visitMethoddef(BSVParser.MethoddefContext ctx) {
        boolean outerContext = actionContext;
        actionContext = true;
	//LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;

        BSVParser.MethodcondContext methodcond = ctx.methodcond();
	if (methodcond != null)
	    typeVisitor.visit(methodcond);

        scope = scopes.pushScope(ctx);
	typeVisitor.pushScope(scope);

	StringBuilder statement = new StringBuilder();
	StringBuilder paramunpack = new StringBuilder();

        String methodName = ctx.name.getText();
	if(ctx.bsvtype() == null) {
            System.err.println("ERROR: Method return type required at " + StaticAnalysis.sourceLocation(ctx));
            return "ERRORETHOD";
        }
	assert ctx.bsvtype() != null : "Method return type required at " + StaticAnalysis.sourceLocation(ctx);
        String returntype = "Void";
        if (ctx.bsvtype() != null) {
            BSVType ty = StaticAnalysis.getBsvType(ctx.bsvtype());
            if (ty != null && !ty.toString().equals("Action"))
                returntype = bsvTypeToKami(ty);
        }
        statement.append("METHOD");
        if (returntype == "Void")
            statement.append("/Action");
        statement.append(" " + methodName);
	int numArgs = 0;
        if (ctx.methodformals() != null) {
	    numArgs = ctx.methodformals().methodformal().size();
            statement.append(" ( ");
            String sep = "";
            for (BSVParser.MethodformalContext formal: ctx.methodformals().methodformal()) {
                if(formal.bsvtype() == null) {
                     System.err.println("ERROR: formalparam null");
                     break;
                }
                BSVType bsvtype = typeVisitor.visit(formal.bsvtype());
                String varName = formal.name.getText();
                statement.append(String.format("%s%s %s", sep, bsvtype.toString(), varName));
                sep = ",";
            }
            statement.append(" )");
        }
        if (returntype != "Void") {
            ReturnVisitor returnVisitor = new ReturnVisitor(scope);
            for (BSVParser.StmtContext stmt: ctx.stmt())
                returnVisitor.visit(stmt);
	    StringBuilder expression = new StringBuilder();
            if (returnVisitor.returnExpr != null)
                expression.append(visit(returnVisitor.returnExpr.expression()));
            else if (ctx.expression() != null)
                expression.append(visit(ctx.expression()));
            else
                expression.append("0");
            statement.append(" " + returntype + " = (" + expression.toString() + ")");
        }
	if (methodcond != null) {
            String methodcondValue = visit(methodcond);
            statement.append(" if (" + methodcondValue + ")");
        }
	statement.append(" {\n");
	statement.append(paramunpack.toString());

        RegReadVisitor regReadVisitor = new RegReadVisitor(scope);
	if (methodcond != null)
	    regReadVisitor.visit(methodcond);
        for (BSVParser.StmtContext stmt: ctx.stmt())
            regReadVisitor.visit(stmt);
        if (ctx.expression() != null)
            regReadVisitor.visit(ctx.expression());
	statements = new ArrayList<>();
	if (methodcond != null) {
            if (statements.size() > 0) {
                for (String s: statements) {
                    statement.append("QQ2           ");
                    statement.append(s);
                    statement.append(newline);
                }
                statements.clear();
            }
	}
        for (BSVParser.StmtContext stmt: ctx.stmt())
            visit(stmt);
	boolean hasStatements = statements.size() > 0;
        if (hasStatements)
	    statement.append("   " + String.join(newline + "   ", statements) + "\n"); // QQ9
	statement.append("    }");
	for (String item: nextMethod) {
             statement.append(item);
        }
        nextMethod.clear();

        actionContext = outerContext;
	statements  = parentStatements;
	statements.add(statement.toString());
	typeVisitor.popScope();
        scope = scopes.popScope();
        return null;
    }

    @Override public String visitRegwrite(BSVParser.RegwriteContext regwrite) {
	typeVisitor.pushScope(scope);

	StringBuilder statement = new StringBuilder();
	BSVParser.ExpressionContext rhs = regwrite.rhs;
	BSVType rhsType = typeVisitor.visit(rhs);
	typeVisitor.visit(regwrite);

	    String regName = regwrite.lhs.getText();
	    SymbolTableEntry entry = scope.lookup(regName);
	    statement.append("        STORE " + blockCondition + " : ");
	    statement.append(visit(regwrite.lhs));
	    statement.append(" = ");
	    statement.append(visit(regwrite.rhs));
	    statement.append(" ");
	    statements.add(statement.toString());
	typeVisitor.popScope();
        return null;
    }

    @Override public String visitStmt(BSVParser.StmtContext ctx) {
	if (ctx.expression() != null) {
	    typeVisitor.pushScope(scope);
	    BSVType exprType = typeVisitor.visit(ctx.expression());
	    System.err.println(String.format("GenerateIR stmt expr type %s at %s", exprType, StaticAnalysis.sourceLocation(ctx)));
	    typeVisitor.popScope();
	    BSVParser.CallexprContext call = getCall(ctx.expression());
	    if (call != null) {
		// call is performed for side effect, so visit it but ignore the expression it returns
		String unusedValue = visit(ctx.expression());
	    } else {
                String ret = visit(ctx.expression());
                if (!ret.equals(""))
		    statements.add(ret);
	    }
	} else {
	    visitChildren(ctx);
	}
	return null;
    }

    @Override public String visitVarassign(BSVParser.VarassignContext ctx) {
	StringBuilder statement = new StringBuilder();
        statement.append("        Assign ");
        boolean multi = ctx.lvalue().size() > 1;
        int count = 0;
        if (multi) statement.append("{ ");
        for (BSVParser.LvalueContext lvalue: ctx.lvalue()) {
            if (multi && count > 0) statement.append(", ");
            statement.append(lvalue.getText());
            count++;
        }
        if (multi) statement.append(" }");
	statement.append(" " + ctx.op.getText() + " ");
        statement.append(visit(ctx.expression()));

	statements.add(statement.toString());
	return null;
    }

    @Override
    public String visitIfstmt(BSVParser.IfstmtContext ctx) {
        LetBindings parentLetBindings = letBindings;
        ArrayList<String> parentStatements = statements;
        letBindings = new LetBindings();
        statements = new ArrayList<>();
        String previousCondition = blockCondition;

	typeVisitor.pushScope(scope);
	typeVisitor.visit(ctx.expression());
	typeVisitor.popScope();

	String predicate = "( " + visit(ctx.expression()) + " )";

        assert(letBindings.size() == 0) : "Unexpected let bindings at " + StaticAnalysis.sourceLocation(ctx) + "\n" + String.join("\n", letBindings);

        StringBuilder statement = new StringBuilder();
        if (previousCondition.equals(""))
            blockCondition = predicate;
        else
            blockCondition = "( " + previousCondition + " & " + predicate + " )";
	System.err.println(String.format("if stmts %d bindings %d at %s",
					 statements.size(), letBindings.size(), StaticAnalysis.sourceLocation(ctx)));
        visit(ctx.stmt(0));
        statement.append(String.join(";\n        ", statements));
        if (ctx.stmt(1) != null) {
            letBindings = new LetBindings();
            statements = new ArrayList<>();
            predicate = "( !" + predicate + " )";
            if (previousCondition.equals(""))
                blockCondition = predicate;
            else
                blockCondition = "( " + previousCondition + " & " + predicate + " )";
            visit(ctx.stmt(1));
            assert(letBindings.size() == 0);
            statement.append(String.join(";\n        ", statements));
	}

        letBindings = parentLetBindings;
        statements  = parentStatements;
        if (statements == null)
            System.err.println("Not gathering statements at " + StaticAnalysis.sourceLocation(ctx));

        statements.add(statement.toString());
        blockCondition = previousCondition;
        return null;
    }

    String destructurePattern(BSVParser.PatternContext pattern, String match, String tagName) {
        if (pattern.taggedunionpattern() != null) {
            BSVParser.TaggedunionpatternContext taggedunionpattern = pattern.taggedunionpattern();
	    tagName = taggedunionpattern.tag.getText();
	    System.err.println(String.format("Matching %s looking up tag %s for pattern %s at %s", match, tagName, pattern.getText(),
					     StaticAnalysis.sourceLocation(pattern)));
            SymbolTableEntry tagEntry = scope.lookup(tagName);
	    assert tagEntry != null : String.format("No entry for pattern tag %s at %s", tagName, StaticAnalysis.sourceLocation(pattern));
	    BSVType tagType = tagEntry.type;
	    BSVParser.PatternContext pat = taggedunionpattern.pattern();
            if (pat != null) {
		if (pat.var != null) {
		    String fieldName = pat.var.getText();
		    return String.format("            LET %1$s <- (#%2$s . %5$s) ;",
					 fieldName,
					 match,
					 tagType.name,
					 ((tagType.params.size() > 0) ? String.format(" %s", bsvTypeToKami(tagType.params.get(0))) : ""),
					 ((tagName != null) ? tagName : ""));
		} else {
		    return "(* FIXME tagged union pattern *)" +
			destructurePattern(taggedunionpattern.pattern(),
					      match,
					      taggedunionpattern.tag.getText());
		}
	    }
	    else {
		// nothing to fetch from the struct representing the tagged union
		return "";
	    }
        } else if (pattern.structpattern() != null) {
            BSVParser.StructpatternContext structpattern = pattern.structpattern();
            tagName = structpattern.tag.getText();
            SymbolTableEntry tagEntry = scope.lookup(tagName);
            assert tagEntry != null;
            BSVType tagType = tagEntry.type;
	    StringBuilder patternString = new StringBuilder();
            for (int i = 0; i < structpattern.pattern().size(); i++) {
                String fieldName = structpattern.lowerCaseIdentifier(i).getText();
                BSVParser.PatternContext fieldPattern = structpattern.pattern(i);
                patternString.append(destructurePattern(fieldPattern, String.format("(#%1$s . %3$s%4$s%5$s)", match,
                                                                                    bsvTypeToKami(tagType),
                                                                                    ((tagName != null) ? tagName : ""), // unused in Kami2
                                                                                    ((tagName != null) ? "$" : ""),
                                                                                    fieldName),
                                                        null));
            }
	    return patternString.toString();
        } else if (pattern.lowerCaseIdentifier() != null) {
            return String.format("              LET %s <- %s;%s",
                                 pattern.lowerCaseIdentifier().getText(),
                                 match,
                                 newline);
        } else if (pattern.constantpattern() != null) {
	    return "(* constantpattern " + pattern.getText() + " *)";
	} else if (pattern.tuplepattern() != null) {
	    return "(* tuplepattern " + pattern.getText() + " *)";
	} else if (pattern.pattern() != null) {
	    return destructurePattern(pattern.pattern(), match, tagName);
	}
	return "(* something went wrong *)";
    }

    @Override public String visitCaseexpr(BSVParser.CaseexprContext ctx) {

	LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;
	letBindings = new LetBindings();
	statements = new ArrayList<>();

	typeVisitor.pushScope(scope);
	BSVType exprType = typeVisitor.visit(ctx.expression());

        int branchnum = 0;
	StringBuilder statement = new StringBuilder();

	int itemnum = 0;
	int nitems = ctx.caseexpritem().size();
	assert nitems > 1 : "At least one case item required at " + StaticAnalysis.sourceLocation(ctx);
	BSVParser.CaseexpritemContext lastitem = ctx.caseexpritem(nitems - 1);
	assert lastitem.pattern() == null && lastitem.exprprimary().size() == 0
	    : "Default clause required in case expression at " + StaticAnalysis.sourceLocation(ctx);

	statement.append("(* case expr *)\n");

        for (BSVParser.CaseexpritemContext expritem: ctx.caseexpritem()) {
	    if (itemnum < nitems - 1)
		statement.append("    (IF (");
	    if (expritem.pattern() != null && expritem.pattern().taggedunionpattern() != null) {
		assert expritem.patterncond().size() == 0 : "pattern cond at " + StaticAnalysis.sourceLocation(expritem);
		assert expritem.pattern().taggedunionpattern().pattern() == null
		    : "Case expr cannot handle tagged union pattern destructuring at " + StaticAnalysis.sourceLocation(expritem.pattern());
		statement.append(String.format("(%1$s . $tag)",
					       visit(ctx.expression()),
					       exprType.name,  // unused in Kami2
					       ((exprType.params.size() > 0) ? bsvTypeToKami(exprType.params.get(0)) : "")  // unused in Kami2
					       ));
		statement.append(" == ");
		String tag = expritem.pattern().taggedunionpattern().tag.getText();
		SymbolTableEntry tagEntry = scope.lookup(tag);
		assert tagEntry != null : "Case expr no entry found for tag " + tag;
		IntValue tagValue = (IntValue)tagEntry.value;
		statement.append("$");
		statement.append(tagValue.value);
	    } else if (expritem.exprprimary().size() > 0) {
		int exprnum = 0;
		int nexprs = expritem.exprprimary().size();
		for (BSVParser.ExprprimaryContext expr: expritem.exprprimary()) {
		    if (exprnum > 0)
			statement.append(" || ");
		    if (nexprs > 0)
			statement.append("(");
		    statement.append(visit(ctx.expression()));
		    statement.append(" == ");
		    statement.append(visit(expr));
		    if (nexprs > 0)
			statement.append(")");
		    exprnum++;
		}
	    } else {
		// default
		statement.append(String.format("(* default %d *)", nitems));
	    }
	    if (itemnum < nitems - 1) {
		statement.append(") then ");
		statement.append(newline);
	    }
	    statement.append(visit(expritem.expression()));
	    if (itemnum != nitems - 1)
		statement.append(" else ");
	    statement.append(newline);
	    itemnum++;
	}
	for (int i = 0; i < nitems - 1; i++) {
	    statement.append(")");
	    statement.append(newline);
	}

	typeVisitor.popScope();
	assert letBindings.size() == 0;
	assert statements.size() == 0
	    : "No statements or calls allowed in case expressions at " + StaticAnalysis.sourceLocation(ctx);
	letBindings = parentLetBindings;
	statements  = parentStatements;
        return statement.toString();
    }

    @Override public String visitCasestmt(BSVParser.CasestmtContext ctx) {
	LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;
	letBindings = new LetBindings();
	statements = new ArrayList<>();

	typeVisitor.pushScope(scope);

        int branchnum = 0;
        logger.fine("visitCasestmt " + ctx.getText());
	BSVType matchType = typeVisitor.visit(ctx.expression());
	StringBuilder statement = new StringBuilder();
        for (BSVParser.CasestmtpatitemContext patitem: ctx.casestmtpatitem()) {
            BSVParser.PatternContext pattern = patitem.pattern();
            BSVParser.StructpatternContext structpattern = pattern.structpattern();
            BSVParser.TaggedunionpatternContext taggedunionpattern = pattern.taggedunionpattern();
	    BSVParser.ConstantpatternContext constantpattern = pattern.constantpattern();
            String tagName = null;
	    IntValue tagValue = null;
	    BSVType tagType = null;
	    if (structpattern != null) {
		tagName = structpattern.tag.getText();
	    } else if (taggedunionpattern != null) {
		tagName = taggedunionpattern.tag.getText();
	    } else if (constantpattern != null) {
		tagValue = new IntValue(constantpattern.getText());
	    } else {
		// FIXME
		tagName = pattern.getText();
	    }
	    if (tagValue == null && tagName != null) {
		SymbolTableEntry tagEntry = scope.lookup(tagName);
		assert tagEntry != null: "No pattern tag entry for " + tagName + " at " + StaticAnalysis.sourceLocation(pattern);
		tagType = tagEntry.type;
		assert tagEntry.value != null : String.format("Missing value for tag %s", tagName);
		tagValue = (IntValue)tagEntry.value;
	    }
            statement.append("   CASEIf (");
            statement.append(visit(ctx.expression()));
	    if (tagName != null)
		statement.append(String.format(" . $tag",
				tagType.name,
				((matchType.params.size() > 0) ? bsvTypeToKami(matchType.params.get(0)) : "") // unused in kami2
		));
            statement.append(" == ");
            statement.append(String.format("$%d", tagValue.value));
            statement.append(") then (");
	    statement.append(newline);
            statement.append(destructurePattern(pattern, ctx.expression().getText(), null));
            assert patitem.patterncond().size() == 0;

	    letBindings = new LetBindings();
	    statements = new ArrayList<>();
            visit(patitem.stmt());
	    assert(letBindings.size() == 0);
            for (String substatement: statements) {
                statement.append(substatement);
                statement.append(newline);
            }

            //statement.append("        Retv");
	    statement.append(newline);
            statement.append("   ) else (");
	    statement.append(newline);
        }

	for (BSVParser.CasestmtitemContext item: ctx.casestmtitem()) {
	    boolean multivalue = item.expression().size() > 0;
            statement.append("    CASE2If (");
	    if (multivalue)
		statement.append("(");
	    statement.append(visit(item.expression(0)));
	    statement.append(" == ");
	    statement.append(visit(ctx.expression()));
	    if (multivalue)
		statement.append(")");
	    for (int i = 1; i < item.expression().size(); i++) {
		statement.append(" || (");
		statement.append(visit(item.expression(i)));
		statement.append(" == ");
		statement.append(visit(ctx.expression()));
		statement.append(")");
	    }
            statement.append(") then (");
	    statement.append(newline);

	    letBindings = new LetBindings();
	    statements = new ArrayList<>();
            visit(item.stmt());
	    assert(letBindings.size() == 0);
            for (String substatement: statements) {
                statement.append(substatement);
                statement.append(newline);
            }

            //statement.append("        Retv");
	    statement.append(newline);
            statement.append("   ) else (");
	    statement.append(newline);
	}

	assert ctx.casestmtdefaultitem() != null : "default clause required at " + StaticAnalysis.sourceLocation(ctx);
	{
	    letBindings = new LetBindings();
	    statements = new ArrayList<>();
            visit(ctx.casestmtdefaultitem().stmt());
	    assert(letBindings.size() == 0);
            for (String substatement: statements) {
                statement.append(substatement);
                statement.append(newline);
            }
	}
	int numBranches = ctx.casestmtpatitem().size() + ctx.casestmtitem().size();
        for (int i = 0; i < numBranches; i += 1) {
	    //statement.append("        Retv");
	    statement.append(") as retval");
	    if (i < numBranches - 1) {
		statement.append("; Ret #retval");
		statement.append(newline);
	    }
	}

	typeVisitor.popScope();
	letBindings = parentLetBindings;
	statements  = parentStatements;
        statements.add(statement.toString());
	return null;
    }
    @Override
    public String visitPattern(BSVParser.PatternContext ctx) {
        //FIXME
        return ("$" + ctx.getText());
    }

    @Override public String visitForstmt(BSVParser.ForstmtContext ctx) {
	LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;
        scope = scopes.pushScope(ctx);
	typeVisitor.popScope();

	logger.fine(String.format("For stmt at %s", StaticAnalysis.sourceLocation(ctx)));

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
        if(!binop.left.getText().equals(iterationVar)) {
            System.err.println("ERROR: loop condition variable does not match: " + binop.left.getText());
            return "ERRORFOR";
        }
        assert binop.left.getText().equals(iterationVar);
        if(!binop.op.getText().equals("<")) {
            System.err.println("ERROR: Unimplemented for loop condition " + testExpr.getText() + " at " + StaticAnalysis.sourceLocation(testExpr));
            return "ERRORFOR";
        }
        assert binop.op.getText().equals("<"): "Unimplemented for loop condition " + testExpr.getText() + " at " + StaticAnalysis.sourceLocation(testExpr);
        String limitVar = binop.right.getText();

	StringBuilder statement = new StringBuilder();
        String instVar = "__inst$Genvar1";
        String lowerBound = "0";
        String forBody = String.format("FOR$%dBody__ENA", forIndex);
        forIndex = forIndex + 1;
	statement.append("        GENERATE :" + instVar + ",(" + lowerBound + ",(" + instVar + "< (" + limitVar + "), (1), " + forBody);

	letBindings = new LetBindings();
	statements = new ArrayList<>();
        visit(ctx.stmt());
	assert(letBindings.size() == 0);
        nextMethod.add("METHOD/Action " + forBody + " ( " + iterationVarType + " " + iterationVar + " ) {\n");
	for (String substatement: statements) {
	    nextMethod.add(substatement + newline);
	}
        nextMethod.add("}\n");


	letBindings = parentLetBindings;
	statements  = parentStatements;
	typeVisitor.popScope();
        scope = scopes.popScope();

	statements.add(statement.toString());
        return null;
    }

    @Override public String visitProviso(BSVParser.ProvisoContext ctx) {
	String name = ctx.var.getText();
	ArrayList<String> params = new ArrayList<>();
	for (BSVParser.BsvtypeContext bsvtype: ctx.bsvtype()) {
	    //FIXME: Not handling TAdd#, etc...
	    params.add(bsvtype.getText());
	}
	logger.fine(String.format("proviso name=%s", name));

	if (mSizeRelationshipProvisos.containsKey(name)) {
	    assert params.size() >= 2 : String.format("Unexpected proviso %s %d params %s at %s",
						      name, params.size(), params,
						      StaticAnalysis.sourceLocation(ctx));
	    if (params.size() == 3)
		return String.format("REPLACE %s = %s %s %s",
				     params.get(2),
				     params.get(0),
				     mSizeRelationshipProvisos.get(name),
				     params.get(1));
	    else
		return String.format("REPLACE %s = %s %s",
				     params.get(1),
				     mSizeRelationshipProvisos.get(name),
				     params.get(0));
	} else if (name.equals("Pos")) {
	    return String.format("CHECK (%2$s > 0)", params.get(0));
	}

	return null;
    }

    @Override public String visitTripleandexpr(BSVParser.TripleandexprContext ctx) {
        if (ctx.expression().size() == 1)
            return visit(ctx.expression(0));
        ArrayList<String> exprs = new ArrayList<>();
        for (BSVParser.ExpressionContext expr: ctx.expression()) {
            exprs.add(visit(expr));
        }
        return String.join(" && ", exprs);
    }

    @Override public String visitCondexpr(BSVParser.CondexprContext ctx) {
	return String.format("(IF %s then %s else %s)",
			     visit(ctx.expression(0)),
			     visit(ctx.expression(1)),
			     visit(ctx.expression(2)));
    }

    @Override public String visitBinopexpr(BSVParser.BinopexprContext expr) {
	if (expr.unopexpr() != null)
	    return (visit(expr.unopexpr()));

	typeVisitor.pushScope(scope);

	assert expr.op != null;
	assert expr.right != null;

	String op = expr.op.getText();
	String leftValue = visit(expr.left);
	String rightValue = visit(expr.right);
	BSVType leftType = typeVisitor.visit(expr.left);
	BSVType rightType = typeVisitor.visit(expr.right);
	if (op.equals(">>") || op.equals("<<")) {
	    String leftWidth = bsvTypeSize(leftType, expr.left);
	    String rightWidth = bsvTypeSize(rightType, expr.right);
	    String kamiOp = (op.equals(">>") ? "Srl" : "Sll");
	    return String.format("(BinBit (%5$s %1$s %2$s) %3$s %4$s)",
				 leftWidth, rightWidth,
				 leftValue, rightValue,
				 kamiOp);
	}

	StringBuilder expression = new StringBuilder();
	expression.append("(");
	if (!inModule && false) {
	    if (expr.op != null) {
		if (op.equals("<"))
		    op = "bitlt";
		expression.append(op);
	    }
	    expression.append(" ");
	}
	if (expr.left != null)
	    expression.append(leftValue);
	if (inModule || true) {
	    if (op.equals("&"))
		op = "~&";
	    else if (op.equals("|"))
		op = "~|";
	    else if (op.equals("^"))
		op = "~+";
	    expression.append(" ");
	    expression.append(op);
	    expression.append(" ");
	} else {
	    expression.append(" ");
	}
	expression.append(rightValue);
	expression.append(")");

	typeVisitor.popScope();
        return expression.toString();
    }
    @Override public String visitUnopexpr(BSVParser.UnopexprContext ctx) {
	StringBuilder expression = new StringBuilder();
        if (ctx.op != null) {
	    String op = ctx.op.getText();
	    expression.append("(");
	    if (op.equals("~")) {
		typeVisitor.pushScope(scope);
		BSVType exprType = typeVisitor.visit(ctx.exprprimary());
		String exprSize = bsvTypeSize(exprType, ctx.exprprimary());
		typeVisitor.popScope();
		op = String.format("UniBit (Neg %1$s) ", exprSize);
	    }
	    if (op.equals("-")) {
		typeVisitor.pushScope(scope);
		BSVType exprType = typeVisitor.visit(ctx.exprprimary());
		String exprSize = bsvTypeSize(exprType, ctx.exprprimary());
		typeVisitor.popScope();
		op = String.format("BinBit (Sub %1$s) $$(natToWord %1$s 0) ", exprSize);
	    }
            expression.append(op);
        }
	expression.append(visit(ctx.exprprimary()));
	if (ctx.op != null)
	    expression.append(")");
	return expression.toString();
    }

    @Override public String visitBitconcat(BSVParser.BitconcatContext ctx) {
	typeVisitor.pushScope(scope);
	if (ctx.expression().size() == 1)
	    return visit(ctx.expression(0));

	BSVParser.ExpressionContext leftarg = ctx.expression(0);
	BSVType leftargType = typeVisitor.visit(leftarg);
	String leftargSize = bsvTypeSize(leftargType, leftarg);
	String leftexpr = visit(leftarg);

	List<String> argSizes = new ArrayList<>();
	argSizes.add(leftargSize);
	for (int i = 1; i < ctx.expression().size(); i++) {
	    BSVParser.ExpressionContext rightarg = ctx.expression(i);
	    BSVType rightargType = typeVisitor.visit(rightarg);
	    String rightargSize = bsvTypeSize(rightargType, rightarg);
	    argSizes.add(rightargSize);
	    leftexpr = String.format("(BinBit (Concat (%1$s) %2$s) %3$s %4$s)",
				     leftargSize,
				     rightargSize,
				     leftexpr,
				     visit(rightarg));
	    leftargSize = String.join(" + ", argSizes);
	}
	typeVisitor.popScope();
	return String.format((useAbstractOmega
			      ? "castBits _ (%1$s) (%1$s) _ %2$s"
			      : "%2$s"),
			     leftargSize, leftexpr);
    }

    @Override public String visitStructexpr(BSVParser.StructexprContext ctx) {
	StringBuilder expression = new StringBuilder();
	String tagName = ctx.tag.getText();
        expression.append(tagName + " { ");
        int i = 0;
	SymbolTableEntry structTypeEntry = scope.lookupType(tagName);
	assert structTypeEntry != null : String.format("No symbol table entry for type %s at %s",
						       tagName, StaticAnalysis.sourceLocation(ctx.tag));
        for (Map.Entry<String,SymbolTableEntry> iterator: structTypeEntry.mappings.bindings.entrySet()) {
	    String fieldName = iterator.getKey();
	    for (BSVParser.MemberbindContext memberbind : ctx.memberbinds().memberbind()) {
		String memberName = memberbind.field.getText();
		if (!fieldName.equals(memberName))
		    continue;
		expression.append(String.format("\"%s\" ::= (%s)%s",
						memberName,
						visit(memberbind.expression()),
						((i == ctx.memberbinds().memberbind().size() - 1) ? " " : " ; ")));
		i++;
	    }
	}
        expression.append(" }");
        return expression.toString();
    }
    @Override public String visitTaggedunionexpr(BSVParser.TaggedunionexprContext ctx) {
	StringBuilder expression = new StringBuilder();
        String tagName = ctx.tag.getText();
	String sourceLocation = StaticAnalysis.sourceLocation(ctx);
        expression.append(String.format("(* tagged union *) STRUCT %s { ", tagName));
        SymbolTableEntry tagEntry = scope.lookup(tagName);
        assert tagEntry != null;
        BSVType tagtype = tagEntry.type.fresh();
        assert tagEntry.value != null : String.format("Missing value for tag %s", tagName);
        IntValue tagValue = (IntValue)tagEntry.value;
        SymbolTableEntry typedefEntry = scope.lookupType(tagtype.name);
        assert typedefEntry != null:
	    String.format("tagged union tag %s expr %s type %s at %s", tagName, ctx.getText(), tagtype, sourceLocation);
        ArrayList<String> visitedFields = new ArrayList<>();

	typeVisitor.pushScope(scope);
	BSVType exprtype = typeVisitor.visit(ctx);
	typeVisitor.popScope();
	TreeMap<String,BSVType> tagtypevars = tagtype.getFreeVariables();
	try {
	    tagtype.unify(exprtype);
	} catch (InferenceError e) {
	    logger.fine(e.toString());
	    System.err.println(e.toString() + " at " + StaticAnalysis.sourceLocation(ctx));
	}

	System.err.println(String.format("tagged union tag %s type %s expr type %s at %s",
					 tagName, tagtype, exprtype, sourceLocation));

        expression.append(String.format(" \"$tag\" ::= $%d", tagValue.value));

        visitedFields.add("$tag");
        for (Map.Entry<String,SymbolTableEntry> iterator: typedefEntry.mappings.bindings.entrySet()) {
            String fieldName = iterator.getKey();
            if (ctx.exprprimary() != null) {
                if (fieldName.equals(tagName) && !visitedFields.contains(tagName)) {
                    expression.append(String.format("; \"%s\" ::= ", tagName));
                    expression.append(visit(ctx.exprprimary()));
                    visitedFields.add(tagName);
                }
            } else if (ctx.memberbinds() != null) {
                int i = 0;
                for (BSVParser.MemberbindContext memberbind : ctx.memberbinds().memberbind()) {
                    String memberfieldname = String.format("%s$%s", tagName, memberbind.field.getText());
                    if (fieldName.equals(memberfieldname) && !visitedFields.contains(memberfieldname)) {
                        visitedFields.add(fieldName);
                        expression.append(String.format("; \"%s\" ::= ", memberfieldname));
                        expression.append(visit(memberbind.expression()));
                        i++;
                    }
                }
            }
            if (!visitedFields.contains(fieldName)) {
		SymbolTableEntry fieldEntry = iterator.getValue();
		BSVType fieldType = fieldEntry.type.fresh();
		BSVType fieldTypeInstance = BSVType.instantiate(fieldType, tagtypevars);
		System.err.println(tagtypevars);
		System.err.println(String.format("    field %s fieldType %s fieldTypeInstance %s at %s",
						 fieldName, fieldType, fieldTypeInstance, sourceLocation));

                expression.append(String.format("; \"%s\" ::= $$(getDefaultConst %s) ",
						fieldName,
						bsvTypeToKami(fieldTypeInstance, 1)));
            }
        }
        expression.append(" }");
        return expression.toString();
    }
    @Override public String visitIntliteral(BSVParser.IntliteralContext ctx) {
	IntValue intValue = new IntValue(ctx.IntLiteral().getText());
	long intWidth = intValue.width;
	BSVType bsvType = typeVisitor.visit(ctx).prune();
	if (bsvType.name.equals("Bit")) {
	    BSVType typeWidth = bsvType.params.get(0).prune();
	    //assert !typeWidth.isVar : String.format("Unknown width for type %s at %s", bsvType, StaticAnalysis.sourceLocation(ctx));
	    long widthFromType = 0;
	    try {
		widthFromType = typeWidth.asLong();
	    } catch (NumberFormatException ex) {
		System.err.println("Cannot compute bit width of " + typeWidth + " at " + StaticAnalysis.sourceLocation(ctx));
	    }
	    assert intWidth == 0 || intWidth == widthFromType;
	    intWidth = widthFromType;
	}
	if (intWidth != 0 || intValue.basespec != null || actionContext) {
            return String.format("%1$s %2$s", "",
                                 intToWord(intWidth, intValue.value));
	} else {
	    //FIXME width from type
	    if(intValue.value >= 128) {
                System.err.println("ERROR: Specify width of int literal %d at " + StaticAnalysis.sourceLocation(ctx));
                return "ERRORINTLITERAL";
            }
	    assert (intValue.value < 128) : "Specify width of int literal %d at " + StaticAnalysis.sourceLocation(ctx);
	    return (String.format("$ %d", intValue.value));
	}
    }
    @Override public String visitRealliteral(BSVParser.RealliteralContext ctx) {
        return ("$ (* real *) " + ctx.RealLiteral().getText());
    }
    @Override public String visitUndefinedexpr(BSVParser.UndefinedexprContext ctx) {
	return "Default";
    }
    @Override public String visitReturnexpr(BSVParser.ReturnexprContext ctx) {
        return ""; // jca
    }
    @Override public String visitVarexpr(BSVParser.VarexprContext ctx) {
	StringBuilder expression = new StringBuilder();
        if (ctx.anyidentifier() != null) {
            String varName = ctx.anyidentifier().getText();
            logger.fine("var " + varName + " scope " + scope);
            if (scope.containsKey(varName)) {
                SymbolTableEntry entry = scope.lookup(varName);
		String prefix = "";//#";
		char firstChar = varName.charAt(0);
		if (entry.symbolType == SymbolType.ModuleParam
		    && entry.type.isVar)
		    prefix = "";
		if (entry.isConstT)
		    prefix = "";
		else if (entry.type.name.equals("Integer"))
		    prefix = "";
		else if (firstChar >= 'A' && firstChar <= 'Z')
		    prefix = "";
		if (!actionContext)
		    prefix = "";

                logger.fine("found binding " + varName + " " + entry.type);
                if (entry.type.name.equals("Reg")) {
                    expression.append(varName);
		} else if (varName.equals("True")) {
		    expression.append("true");
		} else if (varName.equals("False")) {
		    expression.append("false");
		} else {
                    expression.append(prefix + varName);
		}
            } else if (varName.equals("True")) {
		expression.append("true");
            } else if (varName.equals("False")) {
		expression.append("false");
	    } else {
		char firstChar = varName.charAt(0);
		if (firstChar >= 'A' && firstChar <= 'Z') {
		    System.err.println("Capital var " + varName);
		    expression.append(varName);
		} else
		    expression.append("#ZZ" + varName);
            }
        }
        return expression.toString();
    }

    @Override public String visitFieldexpr(BSVParser.FieldexprContext ctx) {
	System.err.println(String.format("Visit field expr %s at %s", ctx.getText(), StaticAnalysis.sourceLocation(ctx)));
	typeVisitor.pushScope(scope);

	BSVType exprType = typeVisitor.visit(ctx.exprprimary());
	typeVisitor.popScope();
	return String.format("(%1$s . %3$s)",
			     visit(ctx.exprprimary()),
			     exprType.name, // unused in Kami2
			     ctx.field.getText());
    }

    @Override public String visitArraysub(BSVParser.ArraysubContext ctx) {
	boolean hasSecondArg = (ctx.expression(1) != null);
	BSVType arraytype = typeVisitor.visit(ctx.array);
	System.err.println(String.format("arraysub array %s type %s at %s",
					 ctx.array.getText(), arraytype, StaticAnalysis.sourceLocation(ctx)));
	if (arraytype.name.equals("Vector")) {
	    return String.format("(%1$s @[ %2$s ])", visit(ctx.array), visit(ctx.expression(0)));
        } else {
	    typeVisitor.pushScope(scope);

	    Evaluator evaluator = new Evaluator(scopes, typeVisitor);
	    assert scope != null;
	    Value msb = evaluator.evaluate(ctx.expression(0), scope);
	    Value lsb = (hasSecondArg) ? evaluator.evaluate(ctx.expression(1), scope) : msb;
	    BSVType exprType = typeVisitor.visit(ctx.array);
	    String exprWidth = bsvTypeSize(exprType, ctx.array);

	    if (msb == null) {
		String msbexpr = visit(ctx.expression(0));
		assert !hasSecondArg;
		return String.format("(%1$s $#[ %2$s : %3$d ])",
				     visit(ctx.array), msbexpr, 1);
	    }

	    System.err.println(String.format("secondArg %s hasSecondArg %s msb %s lsb %s at %s",
					     ctx.expression(1), hasSecondArg, msb, lsb, StaticAnalysis.sourceLocation(ctx)));

	    IntValue imsb = (IntValue)msb;
	    IntValue ilsb = (IntValue)lsb;
	    typeVisitor.popScope();
	    return String.format("(%1$s $#[ %2$d : %3$d ])",
				 visit(ctx.array),
				 imsb.value, ilsb.value, exprWidth);
        }
    }

    @Override public String visitLvalue(BSVParser.LvalueContext ctx) {
	StringBuilder expression = new StringBuilder();
        if (ctx.lvalue() != null) {
            expression.append(visit(ctx.lvalue()));
        }
        if (ctx.index != null) {
            expression.append("[");
            expression.append(visit(ctx.index));
            expression.append("]");
        } else if (ctx.msb != null) {
            expression.append("[");
            expression.append(visit(ctx.msb));
            expression.append(", ");
            expression.append(visit(ctx.lsb));
            expression.append("]");
        } else if (ctx.lowerCaseIdentifier() != null) {
            if (ctx.lvalue() != null)
                expression.append(".");
            expression.append(ctx.lowerCaseIdentifier().getText());
        }
        return expression.toString();
    }

    void instantiateParameterTypes(BSVType functionType, List<BSVParser.ExpressionContext> params, BSVType resultType) {
	functionType = functionType.prune();
	for (BSVParser.ExpressionContext param: params) {
	    if(!functionType.name.equals("Function")) {
		System.err.println("ERROR: Expecting a Function type instead of (" + functionType.name + ") "
		+ functionType + " at " + StaticAnalysis.sourceLocation(param));
                return;
            }
	    assert functionType.name.equals("Function")
		: "Expecting a Function type instead of (" + functionType.name + ") "
		+ functionType + " at " + StaticAnalysis.sourceLocation(param);
	    BSVType paramType = typeVisitor.visit(param);
	    BSVType argType = functionType.params.get(0);
	    try {
		argType.unify(paramType);
	    } catch (InferenceError e) {
		    logger.fine(e.toString());
	    }
	    functionType = functionType.params.get(1).prune();
	}
	System.err.println(String.format("instantiate result type %s with %s", functionType, resultType));
	try {
	    functionType.unify(resultType);
	} catch (InferenceError e) {
	    logger.fine(e.toString());
	}
    }

    String translateCall(BSVParser.CallexprContext ctx) {
	assert ctx != null;
	assert ctx.fcn != null : "Expecting a function call " + ctx.getText() + " at " + StaticAnalysis.sourceLocation(ctx);
        InstanceNameVisitor inv = new InstanceNameVisitor(scopes);
	inv.pushScope(scope);
        String methodName = inv.visit(ctx.fcn);
	BSVType argType = new BSVType();
	BSVType callResultType = typeVisitor.visit(ctx);
	BSVType resultType = callResultType;
	if (inv.methodsUsed.size() > 0) {
	    System.err.println(String.format("First key %s", inv.methodsUsed.firstKey()));
	    InstanceEntry instanceEntry = inv.methodsUsed.get(inv.methodsUsed.firstKey());

	    BSVType methodType = instanceEntry.methodType;
	    if (methodType.name.equals("Function")) {
		argType = methodType.params.get(0);
		resultType = methodType.params.get(1);
	    }
	} else {
	    if( methodName == null) {
                System.err.println("ERROR: No method name at " + StaticAnalysis.sourceLocation(ctx));
                return "CALLERR";
            }
	    assert methodName != null : "No method name at " + StaticAnalysis.sourceLocation(ctx);
	    assert scope != null;
	    SymbolTableEntry functionEntry = scope.lookup(methodName);
	    BSVType functionType = typeVisitor.visit(ctx.fcn);
	    //functionEntry.type.fresh();
	    System.err.println(String.format("Translating call to %s with type %s (result type %s)", methodName, functionType, resultType.prune()));

	    if (functionEntry != null && functionEntry.type.name.equals("Function")) {
		functionType = functionEntry.type.fresh();
		TreeMap<String,BSVType> freeTypeVariables = functionType.getFreeVariables();
		//FIXME: instantiate type
		instantiateParameterTypes(functionType, ctx.expression(), callResultType);
		argType = functionType.params.get(0);
		resultType = functionType.params.get(1);
		System.err.println(String.format("Call expr function %s : %s (%s)\n", methodName, functionType, callResultType));
		StringBuilder typeParameters = new StringBuilder();
		StringBuilder suffixBuilder = new StringBuilder();
		for (Map.Entry<String,BSVType> entry: freeTypeVariables.entrySet()) {
		    typeParameters.append(" ");
		    typeParameters.append(bsvTypeToKami(entry.getValue(), 1));
		    suffixBuilder.append("_");
		    suffixBuilder.append(bsvTypeToIdentifier(entry.getValue()));
		}

		String nameSuffix = suffixBuilder.toString();
		methodBindings.add(String.format("instance'%1$s%2$s := function'%1$s%3$s %1$s%2$s)",
						 methodName,
						 nameSuffix,
						 typeParameters.toString()));
		methodBindings.add(String.format("%1$s%2$s := Interface'%1$s'%1$s instance'%1$s%2$s", methodName, nameSuffix));
		methodName = methodName + nameSuffix;
		//System.err.println("Added methodBindings " + StaticAnalysis.sourceLocation(ctx) + "\n" + String.join("    \n", methodBindings));
	    }
	}
        if (methodName == null)
            methodName = "FIXME$" + ctx.fcn.getText();
        assert methodName != null : "No methodName for " + ctx.fcn.getText();
	StringBuilder statement = new StringBuilder();
            // "Call" is up where the binding is, hopefully
            statement.append(methodName);
	    int argNumber = 0;
	    statement.append(" (");
            String sep = "";
            for (BSVParser.ExpressionContext expr: ctx.expression()) {
		statement.append(sep);
                statement.append(visit(expr));
                if(traceCallm)
		System.err.println(String.format("callm %s arg %d type %s", methodName, argNumber, argType));
		argNumber++;
		if (argNumber < ctx.expression().size()) {
		    if(!resultType.name.equals("Function")) {
                        System.err.println("ERROR: name is not Function:" + resultType.name);
                        return "CALLERROR";
                    }
		    assert (resultType.name.equals("Function"));
		    argType = resultType.params.get(0);
		    resultType = resultType.params.get(1);
		}
                sep = ", ";
            }
	    statement.append(" )");
        return statement.toString();
    }

    @Override public String visitCallexpr(BSVParser.CallexprContext ctx) {
        return translateCall(ctx);
    }

    @Override public String visitValueofexpr(BSVParser.ValueofexprContext ctx) {
	typeVisitor.pushScope(scope);

	BSVType bsvtype = typeVisitor.visit(ctx.bsvtype());
	typeVisitor.popScope();
	return bsvTypeValue(bsvtype, ctx.bsvtype(), 1);
    }

    @Override public String visitBeginendblock(BSVParser.BeginendblockContext ctx) {
	LetBindings parentLetBindings = letBindings;
	ArrayList<String> parentStatements = statements;
	// rule context
        scope = scopes.pushScope(ctx);

	letBindings = new LetBindings();
	statements = new ArrayList<>();
        for (BSVParser.StmtContext stmt: ctx.stmt()) {
            stmtEmitted = true;
            visit(stmt);
        }
	StringBuilder statement = new StringBuilder();
	if (letBindings.size() != 0) {
	    statement.append("        (BKBlock (");
	    statement.append(newline);
	    for (String binding: letBindings) {
		statement.append("        let ");
		statement.append(binding);
		statement.append(" in");
		statement.append(newline);
	    }
	}

	if (letBindings.size() > 0)
	    statement.append("        BKSTMTS {");
	statement.append(newline);
	String separator = (actionContext) ? (newline + "        ") : (newline);
	statement.append(String.join(separator, statements));

	if (letBindings.size() != 0) {
	    statement.append("        }");
	    statement.append("))");
	}

        scope = scopes.popScope();
	letBindings = parentLetBindings;
	statements  = parentStatements;
	statements.add(statement.toString());
        return null;
    }

    BSVType getModuleType(BSVType t) {
	if (t.name.equals("Function")) {
	    return getModuleType(t.params.get(1));
	} else if (t.name.equals("Module")) {
	    return t.params.get(0);
	} else {
	    return t;
	}
    }

    String intToWord(long width, long value) {
	if (value < 128 && width == 0) {
	    return String.format("%d", value);
	} else if (value < 128 && width != 0) {
	    return String.format("%d", value);
	} else {
	    StringBuilder woNotation = new StringBuilder();
	    woNotation.append(String.format("( (* %d'h%x *) WO", width, value));
	    for (int i = 0; i < width; i++)
		woNotation.append(String.format("~%d", (value >> (width - 1 - i)) & 1));
	    woNotation.append(" )");
	    return woNotation.toString();
	}
    }

    public static boolean isKamiKind(BSVType t) {
	if (t.name.equals("Bit")
	    || t.name.equals("Bool")
	    || t.name.equals("UInt")
	    || t.name.equals("Function")
	    || t.name.equals("Vector")
	    || t.name.equals("Void")
	    || t.name.equals("void")
	    )
	    return true;
	// fixme struct
	return false;
    }

    public String bsvTypeToKami(BSVType t) {
        return bsvTypeToKami(t, 0);
    }
    public String bsvTypeToKami(String t) {
	String kamitype = t;
        if (kamitype.equals("Action"))
            kamitype = "Void";
        if (kamitype.equals("Integer"))
            kamitype = "nat";
	else if (kamitype.equals("Bool"))
	    kamitype = "Bit(1)";
	else if (kamitype.equals("Integer"))
	    kamitype = "nat";
	else if (kamitype.equals("Action"))
	    kamitype = "Void";
	else if (kamitype.equals("Vector"))
	    kamitype = "Array";
	else if (kamitype.equals("void"))
	    kamitype = "Void";
	return kamitype;
    }
    public String bsvTypeToKami(BSVType t, int level) {
        if (t == null)
            return "<nulltype>";
        t = t.prune();

	String kamitype = bsvTypeToKami(t.name);
	ArrayList<String> convertedParams = new ArrayList<>();
	for (BSVType p: t.params) {
	    convertedParams.add(bsvTypeToKami(p, 1));
	}
	if (t.name.equals("Action")) {
	    kamitype = "Void";
	} else if (t.name.equals("Integer")) {
	    if (actionContext)
		kamitype = "Bit _";
	    else
		kamitype = "nat";
	} else if (t.name.equals("ActionValue")) {
	    kamitype = convertedParams.get(0);
	} else if (t.name.equals("Vector")) {
	    kamitype = String.format("Array %s", String.join(" ", convertedParams));
	} else if (t.name.equals("TAdd")) {
	    kamitype = String.join(" + ", convertedParams);
	} else if (t.name.equals("TSub")) {
	    kamitype = String.join(" - ", convertedParams);
	} else if (t.name.equals("TDiv")) {
	    kamitype = String.join(" / ", convertedParams);
	} else if (t.name.equals("TLog")) {
	    kamitype = String.format("Nat.log2 %s", convertedParams.get(0));
	} else if (t.name.equals("TExp")) {
	    kamitype = String.format("exp2 %s", convertedParams.get(0));
	} else if (convertedParams.size() > 0) {
	    kamitype = String.format("%s(%s)", t.name, String.join(",", convertedParams));
	}
        return kamitype;
    }

    public String bsvTypeToIdentifier(BSVType t) {
        if (t == null)
            return "<nulltype>";
        t = t.prune();

	String identifier = t.name;
	ArrayList<String> convertedParams = new ArrayList<>();
	for (BSVType p: t.params) {
	    convertedParams.add(bsvTypeToIdentifier(p));
	}
	if (convertedParams.size() > 0) {
	    identifier = String.format("%s_%s_", t.name, String.join("_", convertedParams));
	}
        return identifier;
    }

    String bsvTypeSize(BSVType bsvtype, ParserRuleContext ctx) {
	typeVisitor.pushScope(scope);
	BSVType dereftype = typeVisitor.dereferenceTypedef(bsvtype);
        logger.fine(String.format("bsvtypesize %s dereftype %s at %s", bsvtype, dereftype, StaticAnalysis.sourceLocation(ctx)));
	if (bsvtype.params.size() > 0)
	    dereftype = dereftype.instantiate(dereftype.params, bsvtype.params);
	//System.err.println(String.format("bsvTypeSize %s deref %s", bsvtype, dereftype));
	bsvtype = dereftype;
	String result;
	if (bsvtype.name.equals("Reg") || bsvtype.name.equals("Wire")) {
	    assert bsvtype.params != null;
	    assert bsvtype.params.size() == 1;
	    BSVType elementType = bsvtype.params.get(0);
	    dereftype = typeVisitor.dereferenceTypedef(elementType);
	    if (elementType.params.size() > 0) {
		dereftype = dereftype.instantiate(dereftype.params, elementType.params);
	    }
	    //System.err.println(String.format("bsvtype %s dereftype %s at %s", bsvtype.params.get(0), dereftype, StaticAnalysis.sourceLocation(ctx)));
	    result = bsvTypeSize(dereftype, ctx);
	} else if (bsvtype.name.equals("TAdd")) {
	    result = String.format("(%s + %s)",
				   bsvTypeSize(bsvtype.params.get(0), ctx),
				   bsvTypeSize(bsvtype.params.get(1), ctx));
	} else if (bsvtype.name.equals("TSub")) {
	    result = String.format("(%s - %s)",
				   bsvTypeSize(bsvtype.params.get(0), ctx),
				   bsvTypeSize(bsvtype.params.get(1), ctx));
	} else if (bsvtype.name.equals("TDiv")) {
	    result = String.format("(%s / %s)",
				   bsvTypeSize(bsvtype.params.get(0), ctx),
				   bsvTypeSize(bsvtype.params.get(1), ctx));
	} else if (bsvtype.name.equals("TLog")) {
	    result = String.format("(Nat.log2 %s)",
				   bsvTypeSize(bsvtype.params.get(0), ctx));
	} else if (bsvtype.name.equals("Bit") || bsvtype.name.equals("Int") || bsvtype.name.equals("UInt")) {
	    result = bsvTypeSize(bsvtype.params.get(0), ctx);
	} else if (bsvtype.name.equals("Vector")) {
	    result = String.format("(%s * %s)",
				   bsvTypeSize(bsvtype.params.get(0), ctx),
				   bsvTypeSize(bsvtype.params.get(1), ctx));
	} else {
	    if(!bsvtype.numeric) {
                System.err.println("ERROR: Expecting numeric type, got " + bsvtype + " at " + StaticAnalysis.sourceLocation(ctx));
                return "1";
            }
	    assert bsvtype.numeric : "Expecting numeric type, got " + bsvtype + " at " + StaticAnalysis.sourceLocation(ctx);
	    result = bsvtype.toString();
	}
	typeVisitor.popScope();
	return result;
    }

    String bsvTypeValue(BSVType bsvtype, ParserRuleContext ctx, int level) {
	typeVisitor.pushScope(scope);
	bsvtype = bsvtype.prune();
	BSVType dereftype = typeVisitor.dereferenceTypedef(bsvtype);
        logger.fine(String.format("bsvtypevalue %s dereftype %s at %s", bsvtype, dereftype, StaticAnalysis.sourceLocation(ctx)));
	if (bsvtype.params.size() > 0)
	    dereftype = dereftype.instantiate(dereftype.params, bsvtype.params);
	//System.err.println(String.format("bsvTypeSize %s deref %s", bsvtype, dereftype));
	bsvtype = dereftype;
	String value;
	if (bsvtype.name.equals("TAdd")) {
	    value = String.format("%s + %s",
				  bsvTypeValue(bsvtype.params.get(0), ctx, 1),
				  bsvTypeValue(bsvtype.params.get(1), ctx, 1));
	} else if (bsvtype.name.equals("TSub")) {
	    value = String.format("%s - %s",
				  bsvTypeValue(bsvtype.params.get(0), ctx, 1),
				  bsvTypeValue(bsvtype.params.get(1), ctx, 1));
	} else if (bsvtype.name.equals("TDiv")) {
	    value = String.format("%s / %s",
				  bsvTypeValue(bsvtype.params.get(0), ctx, 1),
				  bsvTypeValue(bsvtype.params.get(1), ctx, 1));
	} else if (bsvtype.name.equals("TLog")) {
	    value = String.format("Nat.log2 %s",
				  bsvTypeValue(bsvtype.params.get(0), ctx, 1));
	} else if (bsvtype.name.equals("TExp")) {
	    value = String.format("exp2 %s",
				  bsvTypeValue(bsvtype.params.get(0), ctx, 1));
	} else if (bsvtype.numeric) {
	    level = 0;
	    value = bsvtype.toString();
	} else {
	    if(!bsvtype.numeric) {
                System.err.println("ERROR: bsvTypeValue expected numeric type, got " + bsvtype + " at " + StaticAnalysis.sourceLocation(ctx));
                return "ERRORTYPEVALUE";
            }
	    assert bsvtype.numeric : "bsvTypeValue expected numeric type, got " + bsvtype + " at " + StaticAnalysis.sourceLocation(ctx);
	    level = 0;
	    value = bsvtype.toString();
	}
	if (level > 0)
	    value = String.format("(%s)", value);
	typeVisitor.popScope();
	return value;
    }

    protected String aggregateResult(String aggregate, String nextResult)
    {
	if (!(aggregate instanceof String) && !(nextResult instanceof String))
	    return null;
	if (aggregate == null)
	    return nextResult;
	if (nextResult == null)
	    return aggregate;
	return aggregate + nextResult;
    }
}
