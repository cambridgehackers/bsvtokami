package bsvtokami;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.*;
import java.util.*;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.tree.*;
import org.antlr.v4.runtime.misc.*;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;

class BSVErrorListener implements ANTLRErrorListener {
    private static Logger logger = Logger.getGlobal();
    @Override
    public void syntaxError(Recognizer<?,?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
	logger.severe(String.format("Syntax error: %s at line %s:%d:%d",
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
    private static Logger logger = Logger.getGlobal();
    Stack<TokenSource> tokenSources = new Stack<>();
    Stack<Boolean> condStack = new Stack<>();
    Stack<Boolean> validStack = new Stack<>();
    HashMap<String,Token> defines = new HashMap<>();
    TokenSource tokenSource = null;
    
    PreprocessedTokenSource() {
	condStack.push(true);
	validStack.push(true);
	Map<String,String> env = System.getenv();
    }
    void define(String ident) {
	defines.put(ident, null);
    }
    void push(TokenSource tokenSource) {
	logger.fine(String.format("pushing token source %s", tokenSource.getSourceName()));
	this.tokenSource = tokenSource;
	tokenSources.push(tokenSource);
    }
    void pop() {
	assert tokenSources.size() > 1;
	tokenSources.pop();
	tokenSource = tokenSources.peek();
	logger.fine(String.format("popped to source %s", tokenSource.getSourceName()));
    }

    String findIncludeFile(String includeName) {
	for (String path: Main.searchDirs) {
	    String filename = String.format("%s/%s", path, includeName);
	    File file = new File(filename);
	    //logger.fine(String.format("Trying %s %s", filename, file.exists()));
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
	    //logger.fine(String.format("token.type %d %s %s:%d", token.getType(), token.getText(), token.getTokenSource().getSourceName(), token.getLine()));
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
			logger.fine(String.format("Defining preprocessor symbol %s %s", identtext, valtoken.getText()));
			defines.put(identtext, valtoken);
			token = null;
			text = null;
		    } else {
			logger.fine(String.format("Defining preprocessor symbol %s", identtext));
			defines.put(identtext, null);
			if (valtoken.getChannel() != 2)
			    return valtoken;
			token = valtoken;
			text = valtoken.getText();
		    }
		}
		if (token == null)
		    continue;

		//logger.fine(String.format("preprocessor channel %d token %s", token.getChannel(), text));
		if (text.equals("`ifdef") || text.equals("`ifndef")) {
		    Token ident = tokenSource.nextToken();
		    String identText = ident.getText();

		    condStack.push(defines.containsKey(identText));
		    if (text.equals("`ifdef"))
			validStack.push(condStack.peek() && validStack.peek());
		    else
			validStack.push(!condStack.peek() && validStack.peek());

		    logger.fine(String.format("preprocessor %s %d %s cond %s valid %s %d",
					      text, ident.getChannel(), identText, condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`else")) {

		    condStack.push(!condStack.pop());
		    validStack.pop();
		    validStack.push(condStack.peek() && validStack.peek());

		    logger.fine(String.format("preprocessor `else cond %s valid %s %d",
						     condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`elsif")) {

		    condStack.pop();
		    validStack.pop();

		    Token ident = tokenSource.nextToken();
		    String identText = ident.getText();
		    condStack.push(defines.containsKey(identText));
		    validStack.push(condStack.peek() && validStack.peek());

		    logger.fine(String.format("preprocessor `elsif %s cond %s valid %s %d",
					      identText, condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`endif")) {
		    condStack.pop();
		    validStack.pop();
		    logger.fine(String.format("preprocessor `endif cond %s valid %s %d",
						     condStack.peek(), validStack.peek(), validStack.size()));
		} else if (text.equals("`include")) {
		    Token filenameToken = tokenSource.nextToken();
		    String include = filenameToken.getText();

		    if (!validStack.peek()) {
			logger.fine("preprocessor skipping include " + include);
			continue;
		    }

		    include = include.substring(1,include.length()-1);
		    String filename = findIncludeFile(include);
		    assert filename != null: String.format("Include %s not found", include);
		    assert !filename.equals("null"): String.format("Include %s not found", include);
		    logger.fine(String.format("preprocessor including %s: %s", include, filename));
		    try {
			CharStream charStream = CharStreams.fromFileName(filename);
			Lexer lexer = new BSVLexer(charStream);
			push(lexer);
		    } catch (IOException ex) {
			logger.severe(ex.toString());
			System.err.println(String.format("Include %s not found", include));
		    }
		} else if (validStack.peek()) {
		    // substitute
		    String identifier = token.getText().substring(1);
		    //logger.fine(String.format("defined %s %s", identifier, defines.containsKey(identifier)));
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
    static ArrayList<String> searchDirs = new ArrayList<>();
    private static PrintStream dotstream;
    static String kamidir; 
    private static Logger logger = Logger.getGlobal();

    static ParserRuleContext parsePackage(String pkgName, String filename) throws IOException {
	System.err.println("parsePackage " + filename);
	File file = new File(filename);
	logger.fine(String.format("Parsing %s %s", pkgName, filename));
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
	parser.removeErrorListeners();
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
System.err.println(String.format("Trying %s %s", filename, file.exists()));
	    if (file.exists())
		return filename;
	}
	assert false : "No file found for package " + pkgName;
	return null;
    }

    static BSVParser.PackagedefContext analyzePackage(String pkgName, String filename, boolean translateToKami) throws IOException {
        System.err.println("STARTPACKAGE: " + pkgName);
	packages.put(pkgName, null); // mark that we are working on this package
	if (!packages.containsKey("Prelude")) {
	    analyzePackage("Prelude", findPackageFile("Prelude"), false);
	}

	System.err.println(String.format("parsePkg %s %s", pkgName, filename));
	ParserRuleContext ctx = parsePackage(pkgName, filename);
	if (dotstream != null) {
	    dotstream.println(String.format("    n%s[label=%s];",
					    pkgName, pkgName));
	}

	BSVParser.PackagedefContext packagedef = (BSVParser.PackagedefContext)ctx;
	for (BSVParser.PackagestmtContext stmt: packagedef.packagestmt()) {
	    BSVParser.ImportdeclContext importdecl = stmt.importdecl();
	    if (importdecl != null) {
		for (BSVParser.ImportitemContext importitem: importdecl.importitem()) {
		    String importedPkgName = importitem.pkgname.getText();
		    logger.fine(String.format("import %s %s at %s",
					      importedPkgName,
					      (packages.containsKey(importedPkgName) ? "previously seen" : "unseen"),
					      StaticAnalysis.sourceLocation(importitem)));
		    if (dotstream != null)
			dotstream.println(String.format("    n%s -> n%s;", pkgName, importedPkgName));
		    if (!packages.containsKey(importedPkgName)) {
			analyzePackage(importedPkgName, findPackageFile(importedPkgName), true);
		    }
		}
	    }
	}
	staticAnalyzer.visitPackage(pkgName, packagedef);
	//Evaluator evaluator = new Evaluator(staticAnalyzer);
	//evaluator.evaluate(packagedef);
	if (translateToKami) {
	    System.err.println(String.format("filename=%s", filename));
	    File file = new File(filename);
	    System.err.println(String.format("filename=%s file=%s", filename, file));
	    System.err.println(String.format("file.getParent()=%s", file.getParent()));
	    String dirname = (kamidir != null) ? kamidir : file.getParent();
	    System.err.println(String.format("kamidir=%s dirname=%s", kamidir, dirname));
	    File dir = new File(dirname);
	    if (!dir.exists()) {
		dir.mkdirs();
	    }
	    File ofile = new File(dirname, pkgName + ".generated.IR");
	    try {
		BSVToKami bsvToKami = new BSVToKami(pkgName, ofile, staticAnalyzer);

		bsvToKami.visit(packagedef);
	    } catch (Exception e) {
		String msg = String.format("Exception while translating file %s: %s", filename, e.toString());
		logger.severe(msg);
		System.err.println(msg);
		e.printStackTrace();
	    } catch (AssertionError e) {
		String msg = String.format("Assertion error while translating file %s: %s", filename, e.toString());
		logger.severe(msg);
		System.err.println(msg);
		e.printStackTrace();
	    }
	}

        System.err.println("ENDPACKAGE: " + pkgName);
	return packagedef;
    }

    public static void main(String[] args) {
	Map<String,String> env = System.getenv();
	Options options = new Options();
	options.addOption(Option.builder("I")
			  .hasArg()
			  .desc("Include path")
			  .build());
	options.addOption(Option.builder("K")
			  .hasArg()
			  .desc("Directory in which to write kami files")
			  .build());

	logger.setLevel(Level.FINE);
	ConsoleHandler consoleHandler = new ConsoleHandler();
	consoleHandler.setLevel(Level.WARNING);
	FileHandler fileHandler;
	try {
	    fileHandler = new FileHandler("bsvtokami.log");
	    fileHandler.setLevel(Level.FINE);
	    logger.addHandler(fileHandler);
	} catch (IOException ex) {
	    logger.warning("Could not log to file: " + ex.toString());
	}
	for (Handler handler: logger.getHandlers())
	    System.err.println("Logger handler " + handler);

	try {
	    CommandLine cmdLine = new DefaultParser().parse(options, args, true);
	    Iterator<Option> iterator = cmdLine.iterator();
	    while (iterator.hasNext()) {
		Option option = iterator.next();
		logger.fine("Option " + option.getOpt());
		if (option.getOpt().equals("I")) {
		    for (String includePath: option.getValues()) {
			logger.info("Including " + includePath);
			searchDirs.add(includePath);
		    }
		} else if (option.getOpt().equals("K")) {
		    kamidir = option.getValue();
		}
	    }
	    for (String arg: cmdLine.getArgs()) {
		logger.fine("Extra args: " + arg);
	    }
	    args = cmdLine.getArgs();
	} catch (ParseException e) {
	    logger.fine("Error parsing command line options " + e);
	    return;
	}

	if (env.containsKey("BSVSEARCHPATH")) {
	    for (String searchDir: env.get("BSVSEARCHPATH").split(":"))
		searchDirs.add(searchDir);
	}

	try {
	    File dotfile = new File("imports.dot");
	    dotstream = new PrintStream(dotfile);
	    dotstream.println("digraph {");
	} catch (FileNotFoundException ex) {
	    logger.severe(ex.toString());
	    dotstream = null;
	}

	packages = new HashMap<>();
        for (String filename: args) {
            logger.fine("converting file " + filename);
            System.err.println("converting file " + filename);
            try {

		File file = new File(filename);
		String[] components = file.getName().split("\\.");
		String pkgName = components[0];

		BSVParser.PackagedefContext packagedef = analyzePackage(pkgName, filename, true);
                System.out.println("");
		logger.fine("finished processing package " + pkgName);

		if (false) {
		    logger.fine("Evaluating module mkMain"); Evaluator evaluator = new Evaluator(staticAnalyzer);
		    evaluator.evaluateModule("mkMain", packagedef);
		    while (!evaluator.isFinished()) {
			evaluator.runRulesOnce();
		    }
		}
            } catch (IOException e) {
                logger.warning("IOException " + e);
            } catch (Exception e) {
                e.printStackTrace();
            } catch (AssertionError e) {
                e.printStackTrace();
            }
        }

	if (dotstream != null) {
	    dotstream.println("    }");
	}
    }
}
