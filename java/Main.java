
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.*;
import org.antlr.v4.runtime.misc.*;

class BSVErrorListener implements ANTLRErrorListener {
    @Override
    public void syntaxError(Recognizer<?,?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
	System.err.println(String.format("Syntax error: %s at line %s:%d:%d",
					 msg, recognizer.getInputStream().getSourceName(), line, charPositionInLine));
    }

    @Override
    public void reportAmbiguity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, boolean exact, BitSet ambigAlts, ATNConfigSet configs) {
    }

    @Override
    public void reportAttemptingFullContext(Parser recognizer, DFA dfa, int startIndex, int stopIndex, BitSet conflictingAlts, ATNConfigSet configs) {
    }

    @Override
    public void reportContextSensitivity(Parser recognizer, DFA dfa, int startIndex, int stopIndex, int prediction, ATNConfigSet configs) {
    }
}

class PreprocessedTokenSource implements TokenSource {
    Stack<TokenSource> tokenSources = new Stack<>();
    Stack<Boolean> condStack = new Stack<>();
    Stack<Boolean> validStack = new Stack<>();
    HashMap<String,Token> defines = new HashMap<>();
    TokenSource tokenSource = null;
    String[] searchDirs = new String[0];
    
    PreprocessedTokenSource() {
	condStack.push(true);
	validStack.push(true);
	Map<String,String> env = System.getenv();
	if (env.containsKey("BSVSEARCHPATH")) {
	    searchDirs = env.get("BSVSEARCHPATH").split(":");
	}
    }
    void define(String ident) {
	defines.put(ident, null);
    }
    void push(TokenSource tokenSource) {
	System.err.println(String.format("pushing token source %s", tokenSource.getSourceName()));
	this.tokenSource = tokenSource;
	tokenSources.push(tokenSource);
    }
    void pop() {
	assert tokenSources.size() > 1;
	tokenSources.pop();
	tokenSource = tokenSources.peek();
	System.err.println(String.format("popped to source %s", tokenSource.getSourceName()));
    }

    String findIncludeFile(String includeName) {
	for (String path: searchDirs) {
	    String filename = String.format("%s/%s", path, includeName);
	    File file = new File(filename);
	    //System.err.println(String.format("Trying %s %s", filename, file.exists()));
	    if (file.exists())
		return filename;
	}
	assert false : "No file found for include " + includeName;
	return null;
    }

    static String sourceLocation(Token token) {
	TokenSource source = token.getTokenSource();
	return String.format("%s:%d", source.getSourceName(), token.getLine());
    }

    @Override
    public int getCharPositionInLine() {
	return tokenSource.getCharPositionInLine();
    }
    @Override
    public CharStream getInputStream() {
	return tokenSource.getInputStream();
    }
    @Override
    public int getLine() {
	return tokenSource.getLine();
    }
    @Override
    public String getSourceName() {
	return tokenSource.getSourceName();
    }
    @Override
    public TokenFactory<?> getTokenFactory() {
	return tokenSource.getTokenFactory();
    }
    @Override
    public Token nextToken() {
	while (true) {
	    Token token = tokenSource.nextToken();
	    //System.err.println(String.format("token.type %d %s %s:%d", token.getType(), token.getText(), token.getTokenSource().getSourceName(), token.getLine()));
	    if (token.getType() == Token.EOF && tokenSources.size() > 1) {
		pop();
		continue;
	    }
	    if (token.getChannel() == 2) {
		String text = token.getText();
		while (text != null && text.equals("`define")) {
		    Token identtoken = tokenSource.nextToken();
		    String identtext = identtoken.getText();
		    Token valtoken = tokenSource.nextToken();
		    if (identtoken.getLine() == valtoken.getLine()) {
			System.err.println(String.format("Defining preprocessor symbol %s %s", identtext, valtoken.getText()));
			defines.put(identtext, valtoken);
			token = null;
			text = null;
		    } else {
			System.err.println(String.format("Defining preprocessor symbol %s", identtext));
			defines.put(identtext, null);
			if (valtoken.getChannel() != 2)
			    return valtoken;
			token = valtoken;
			text = valtoken.getText();
		    }
		}
		if (token == null)
		    continue;

		//System.err.println(String.format("preprocessor channel %d token %s", token.getChannel(), text));
		if (text.equals("`ifdef") || text.equals("`ifndef")) {
		    Token ident = tokenSource.nextToken();
		    String identText = ident.getText();

		    condStack.push(defines.containsKey(identText));
		    if (text.equals("`ifdef"))
			validStack.push(condStack.peek() && validStack.peek());
		    else
			validStack.push(!condStack.peek() && validStack.peek());

		    System.err.println(String.format("preprocessor %s %d %s cond %s valid %s %d",
						     text, ident.getChannel(), identText, condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`else")) {

		    condStack.push(!condStack.pop());
		    validStack.pop();
		    validStack.push(condStack.peek() && validStack.peek());

		    System.err.println(String.format("preprocessor `else cond %s valid %s %d",
						     condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`elsif")) {

		    condStack.pop();
		    validStack.pop();

		    Token ident = tokenSource.nextToken();
		    String identText = ident.getText();
		    condStack.push(defines.containsKey(identText));
		    validStack.push(condStack.peek() && validStack.peek());

		    System.err.println(String.format("preprocessor `elsif %s cond %s valid %s %d",
						     identText, condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`endif")) {
		    condStack.pop();
		    validStack.pop();
		    System.err.println(String.format("preprocessor `endif cond %s valid %s %d",
						     condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`include")) {
		    Token filenameToken = tokenSource.nextToken();
		    String filename = filenameToken.getText();

		    if (!validStack.peek()) {
			System.err.println("preprocessor skipping include " + filename);
			continue;
		    }

		    filename = filename.substring(1,filename.length()-1);
		    filename = findIncludeFile(filename);
		    System.err.println(String.format("preprocessor including %s", filename));
		    try {
			CharStream charStream = CharStreams.fromFileName(filename);
			Lexer lexer = new BSVLexer(charStream);
			push(lexer);
		    } catch (IOException ex) {
			System.err.println(ex);
		    }
		} else if (validStack.peek()) {
		    // substitute
		    String identifier = token.getText().substring(1);
		    //System.err.println(String.format("defined %s %s", identifier, defines.containsKey(identifier)));
		    assert defines.containsKey(identifier) : String.format("No definition for %s at %s",
									   identifier, sourceLocation(token));
		    Token valtoken = defines.get(identifier);
		    return valtoken;
		}
	    } else if (!validStack.peek()) {
		continue;
	    } else {
		return token;
	    }
	}
    }
    @Override
    public void setTokenFactory(TokenFactory<?> factory) {
	tokenSource.setTokenFactory(factory);
    }
}

class Main {
    private static HashMap<String, ParserRuleContext> packages;
    static StaticAnalysis staticAnalyzer = new StaticAnalysis();
    static String[] searchDirs = new String[0];

    static ParserRuleContext parsePackage(String pkgName, String filename) throws IOException {
	File file = new File(filename);
	System.err.println(String.format("Parsing %s %s", pkgName, filename));
	CharStream charStream = CharStreams.fromFileName(filename);

        /*
         * make Lexer
         */
        Lexer lexer = new BSVLexer(charStream);

	PreprocessedTokenSource preprocessedTokenSource = new PreprocessedTokenSource();
	preprocessedTokenSource.push(lexer);
	preprocessedTokenSource.define("BSVTOKAMI");

	CommonTokenStream commonTokenStream = new CommonTokenStream(preprocessedTokenSource);

        /*
         * make a Parser on the token stream
         */
        BSVParser parser = new BSVParser(commonTokenStream);
	parser.addErrorListener(new BSVErrorListener());

	/*
	 * get the top node of the AST. This corresponds to the topmost rule of BSV.g4, "start"
	 */
	ParserRuleContext packagedef = parser.packagedef();
	packages.put(pkgName, packagedef);
	return packagedef;
    }

    static String findPackageFile(String pkgName) {
	for (String path: searchDirs) {
	    String filename = String.format("%s/%s.bsv", path, pkgName);
	    File file = new File(filename);
	    if (file.exists())
		return filename;
	}
	assert false : "No file found for package " + pkgName;
	return null;
    }

    static BSVParser.PackagedefContext analyzePackage(String pkgName, String filename) throws IOException {
	packages.put(pkgName, null); // mark that we are working on this package
	if (!packages.containsKey("Prelude")) {
	    analyzePackage("Prelude", findPackageFile("Prelude"));
	}

	ParserRuleContext ctx = parsePackage(pkgName, filename);
	BSVParser.PackagedefContext packagedef = (BSVParser.PackagedefContext)ctx;
	for (BSVParser.PackagestmtContext stmt: packagedef.packagestmt()) {
	    BSVParser.ImportdeclContext importdecl = stmt.importdecl();
	    if (importdecl != null) {
		for (BSVParser.ImportitemContext importitem: importdecl.importitem()) {
		    String importedPkgName = importitem.pkgname.getText();
		    System.err.println(String.format("import %s %s at %s",
						     importedPkgName,
						     (packages.containsKey(importedPkgName) ? "previously seen" : "unseen"),
						     StaticAnalysis.sourceLocation(importitem)));
		    if (!packages.containsKey(importedPkgName)) {
			analyzePackage(importedPkgName, findPackageFile(importedPkgName));
		    }
		}
	    }
	}
	staticAnalyzer.visitPackage(pkgName, packagedef);
	Evaluator evaluator = new Evaluator(staticAnalyzer);
	evaluator.evaluate(packagedef);
	return packagedef;
    }

    public static void main(String[] args) {
	Map<String,String> env = System.getenv();
	if (env.containsKey("BSVSEARCHPATH")) {
	    searchDirs = env.get("BSVSEARCHPATH").split(":");
	}
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
		evaluator.evaluateModule("mkMain", packagedef);
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
