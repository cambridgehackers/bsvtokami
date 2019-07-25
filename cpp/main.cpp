/* Copyright (c) 2012-2017 The ANTLR Project. All rights reserved.
 * Use of this file is governed by the BSD 3-clause license that
 * can be found in the LICENSE.txt file in the project root.
 */

//
//  main.cpp
//

#include <stdlib.h>
#include <unistd.h>
#include <iostream>

#include "antlr4-runtime.h"
#include "BSVLexer.h"
#include "BSVParser.h"
#include "GenerateAst.h"
#include "TypeChecker.h"

using namespace antlr4;

void usage(char *const argv[]) {
    fprintf(stderr, "Usage: %s [-t]\n", argv[0]);
    exit(-1);
}

int main(int argc, char *const argv[]) {
    bool dumptokens = false;
    bool dumptree = false;
    size_t numberOfSyntaxErrors = 0;

    int ch;
    int opt_type_check = 0;
    int opt_ast = 1;
    while ((ch = getopt(argc, argv, "at")) != -1) {
        switch (ch) {
            case 'a':
                opt_ast = 1;
                break;
            case 't':
                opt_type_check = 1;
                break;
            default:
                usage(argv);
        }
    }

    for (int i = optind; i < argc; i++) {
        std::cerr << "Parsing file " << argv[i] << std::endl;
        std::string inputFileName(argv[i]);
        ANTLRFileStream input(inputFileName);
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
        BSVParser::PackagedefContext *tree = parser.packagedef();
        numberOfSyntaxErrors += parser.getNumberOfSyntaxErrors();
        if (dumptree) {
            std::cout << tree->toStringTree(&parser) << std::endl << std::endl;
        }
        if (opt_type_check) {
            TypeChecker *typeChecker = new TypeChecker();
            typeChecker->visit(tree);
        }
        if (opt_ast) {
            GenerateAst *generateAst = new GenerateAst();
            generateAst->generateAst(tree);
        }
    }
    return (numberOfSyntaxErrors == 0) ? 0 : 1;
}
