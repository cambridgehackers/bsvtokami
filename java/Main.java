
import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

class Main {
    public static void main(String[] args) {
        /*
         * make Lexer
         */
        Lexer lexer = null;

        /*
         * make a Parser on the token stream
         */
        BSVParser parser = null;

        for (String filename: args) {
            System.err.println("converting file " + filename);
            try {

                File file = new File(filename);
                String[] components = file.getName().split("\\.");
                String pkgName = components[0];
		System.err.println("Path " + file.getParent());
		File ofile = new File(file.getParent(), pkgName + ".v");

                CharStream charStream = CharStreams.fromFileName(filename);

                if (lexer == null) {
                    lexer = new BSVLexer(charStream);
                    parser = new BSVParser(new CommonTokenStream(lexer));
                } else {
                    lexer.setInputStream(charStream);
                    parser.setTokenStream(new CommonTokenStream(lexer));
                }

                /*
                 * get the top node of the AST. This corresponds to the topmost rule of BSV.g4, "start"
                 */
                ParserRuleContext packagedef = parser.packagedef();

                StaticAnalysis staticAnalysis = new StaticAnalysis();
                staticAnalysis.visit(packagedef);

                BSVToKami bsvToKami = new BSVToKami(pkgName, ofile, staticAnalysis);

                bsvToKami.visit(packagedef);
                System.out.println("");
		System.err.println("finished processing package " + pkgName);

		System.err.println("Evaluating module main"); Evaluator evaluator = new Evaluator(staticAnalysis);
		evaluator.evaluate("main", packagedef);


            } catch (IOException e) {
                System.err.println("IOException " + e);
            } catch (Exception e) {
                e.printStackTrace();
            }
        }

    }
}
