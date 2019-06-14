/* Copyright (c) 2012-2017 The ANTLR Project. All rights reserved.
 * Use of this file is governed by the BSD 3-clause license that
 * can be found in the LICENSE.txt file in the project root.
 */

//
//  main.cpp
//

#include <iostream>

#include "antlr4-runtime.h"
#include "BSVLexer.h"
#include "BSVParser.h"
#include "StaticAnalyzer.h"
#include "TypeChecker.h"

using namespace antlr4;

int main(int argc, const char **argv) {
    bool dumptokens = false;
    bool dumptree = false;
    size_t numberOfSyntaxErrors = 0;
    for (int i = 1; i < argc; i++) {
	std::cout << "Parsing file " << argv[i] << std::endl;
	ANTLRFileStream input(std::string(argv[i]));
	BSVLexer lexer(&input);
	CommonTokenStream tokens(&lexer);

	tokens.fill();
	if (dumptokens) {
	    for (auto token : tokens.getTokens()) {
		std::cout << token->toString() << std::endl;
	    }
	}

	BSVParser parser(&tokens);
	//parser.addErrorListener(&ConsoleErrorListener::INSTANCE);
	tree::ParseTree* tree = parser.packagedef();
	numberOfSyntaxErrors += parser.getNumberOfSyntaxErrors();
	if (dumptree) {
	    std::cout << tree->toStringTree(&parser) << std::endl << std::endl;
	}
	StaticAnalyzer *staticAnalyzer = new StaticAnalyzer();
	staticAnalyzer->visit(tree);
	TypeChecker *typeChecker = new TypeChecker();
	typeChecker->visit(tree);
    }
    return (numberOfSyntaxErrors == 0) ? 0 : 1;
}
