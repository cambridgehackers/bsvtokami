
import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

class Main {
   public static void main(String[] args) {
      try {
	  File file = new File(args[0]);
	  String[] components = file.getName().split("\\.");
	  String pkgName = components[0];
	  CharStream charStream = CharStreams.fromFileName(args[0]);
         /*
          * make Lexer
          */
	  Lexer lexer = new BSVLexer(charStream);
         /*
          * get a TokenStream on the Lexer
          */
         TokenStream tokenStream = new CommonTokenStream(lexer);

         /*
          * make a Parser on the token stream
          */
         BSVParser parser = new BSVParser(tokenStream);
         /*
          * get the top node of the AST. This corresponds to the topmost rule of BSV.g4, "start"
          */
         ParserRuleContext packagedef = parser.packagedef();
	 
	 StaticAnalysis staticAnalysis = new StaticAnalysis();
	 staticAnalysis.visit(packagedef);

	 BSVToKami bsvToKami = new BSVToKami(pkgName, staticAnalysis);
	 
	 bsvToKami.visit(packagedef);

      } catch (IOException e) {
         e.printStackTrace();
      }
   }
}
