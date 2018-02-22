
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

class Main {
    private static HashMap<String, ParserRuleContext> packages;
    static StaticAnalysis staticAnalyzer = new StaticAnalysis();

    static ParserRuleContext parsePackage(String pkgName, String filename) throws IOException {
	File file = new File(filename);
	CharStream charStream = CharStreams.fromFileName(filename);

        /*
         * make Lexer
         */
        Lexer lexer = new BSVLexer(charStream);

        /*
         * make a Parser on the token stream
         */
        BSVParser parser = new BSVParser(new CommonTokenStream(lexer));

	/*
	 * get the top node of the AST. This corresponds to the topmost rule of BSV.g4, "start"
	 */
	ParserRuleContext packagedef = parser.packagedef();
	packages.put(pkgName, packagedef);
	return packagedef;
    }

    static String findPackageFile(String pkgName) {
	return String.format("lib/%s.bsv", pkgName);
    }

    static BSVParser.PackagedefContext analyzePackage(String pkgName, String filename) throws IOException {
	packages.put(pkgName, null); // mark that we are working on this package
	if (!packages.containsKey("Prelude")) {
	    analyzePackage("Prelude", findPackageFile("Prelude"));
	}

	ParserRuleContext ctx = parsePackage(pkgName, filename);
	BSVParser.PackagedefContext packagedef = (BSVParser.PackagedefContext)ctx;
	for (BSVParser.PackagestmtContext stmt: packagedef.packagestmt()) {
	    if (stmt.getRuleIndex() == BSVParser.RULE_importdecl) {
		BSVParser.ImportdeclContext importdecl = stmt.importdecl();
		for (BSVParser.ImportitemContext importitem: importdecl.importitem()) {
		    String importedPkgName = importitem.pkgname.getText();
		    if (!packages.containsKey(importedPkgName)) {
			analyzePackage(importedPkgName, findPackageFile(importedPkgName));
		    }
		}
	    }
	}
	staticAnalyzer.visitPackage(pkgName, packagedef);
	Evaluator evaluator = new Evaluator(staticAnalyzer);
	evaluator.evaluate(pkgName, packagedef);
	return packagedef;
    }

    public static void main(String[] args) {
	packages = new HashMap<>();
        for (String filename: args) {
            System.err.println("converting file " + filename);
            try {

		File file = new File(filename);
		String[] components = file.getName().split("\\.");
		String pkgName = components[0];

		BSVParser.PackagedefContext packagedef = analyzePackage(pkgName, filename);

		File ofile = new File(file.getParent(), pkgName + ".v");
                BSVToKami bsvToKami = new BSVToKami(pkgName, ofile, staticAnalyzer);

                bsvToKami.visit(packagedef);
                System.out.println("");
		System.err.println("finished processing package " + pkgName);

		System.err.println("Evaluating module mkMain"); Evaluator evaluator = new Evaluator(staticAnalyzer);
		evaluator.evaluate("mkMain", packagedef);
		while (!evaluator.isFinished()) {
		    evaluator.runRulesOnce();
		}
            } catch (IOException e) {
                System.err.println("IOException " + e);
            } catch (Exception e) {
                e.printStackTrace();
            } catch (AssertionError e) {
                e.printStackTrace();
            }
        }

    }
}
