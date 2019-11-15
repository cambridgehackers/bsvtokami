/* Copyright (c) 2012-2017 The ANTLR Project. All rights reserved.
 * Use of this file is governed by the BSD 3-clause license that
 * can be found in the LICENSE.txt file in the project root.
 */

//
//  main.cpp
//
#include <libgen.h>
#include <iostream>
#include <stdlib.h>
#include <unistd.h>
#include <string>
#include <sys/stat.h>

//#include <boost/filesystem.hpp>


#include "antlr4-runtime.h"
#include "BSVLexer.h"
#include "BSVParser.h"
#include "BSVPreprocessor.h"
#include "GenerateAst.h"
#include "GenerateKami.h"
#include "GenerateKoika.h"
#include "GenerateIR.h"
#include "Inliner.h"
#include "TypeChecker.h"

using namespace antlr4;
//namespace fs = boost::filesystem;

void usage(char *const argv[]) {
    fprintf(stderr, "Usage: %s [-t]\n", argv[0]);
    exit(-1);
}

int main(int argc, char *const argv[]) {
    bool dumptokens = false;
    bool dumptree = false;
    size_t numberOfSyntaxErrors = 0;

    int ch;
    int opt_type_check = 1;
    int opt_ast = 1;
    int opt_kami = 1;
    int opt_koika = 1;
    int opt_ir = 0;
    int opt_inline = 0;
    string opt_rename;
    while ((ch = getopt(argc, argv, "Iair:t")) != -1) {
        switch (ch) {
            case 'a':
                opt_ast = 1;
                break;
            case 'i':
                opt_ir = 1;
                break;
            case 'k':
                opt_kami = 1;
                break;
            case 'K':
                opt_koika = 1;
                break;
            case 'I':
                opt_inline = 1;
                break;
            case 'r':
                opt_rename = string(optarg);
                break;
            case 't':
                opt_type_check = 1;
                break;
            default:
                usage(argv);
        }
    }

    for (int i = optind; i < argc; i++) {
        string inputFileName(argv[i]);
        std::cerr << "Parsing file -1- " << inputFileName << std::endl;
        BSVPreprocessor preprocessor(inputFileName);
        CommonTokenStream tokens((TokenSource *) &preprocessor);

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
        if (opt_ast) {
            shared_ptr<TypeChecker> typeChecker(new TypeChecker());
            typeChecker->visit(tree);
            GenerateAst *generateAst = new GenerateAst(typeChecker);
            shared_ptr<PackageDefStmt> packageDef = generateAst->generateAst(tree);;
            vector<shared_ptr<Stmt>> stmts = packageDef->stmts;
            if (opt_kami) {
                ::mkdir("kami", 0755);

                string kamiFileName("kami/");
                char buffer[4096];
                kamiFileName += string(::basename_r(inputFileName.c_str(), buffer));
                kamiFileName += string(".kami");
                GenerateKami *generateKami = new GenerateKami();
                generateKami->open(kamiFileName);
                generateKami->generateStmts(stmts);
                generateKami->close();
            }
            if (opt_koika) {
                ::mkdir("koika", 0775);

                string koikaFileName("koika/");
                char buffer[4096];
                koikaFileName += string(::basename_r(inputFileName.c_str(), buffer));
                koikaFileName += string(".koika");

                GenerateKoika *generateKoika = new GenerateKoika();
                generateKoika->open(koikaFileName);
                generateKoika->generateStmts(stmts);
                generateKoika->close();
            }
            if (opt_ir) {
                GenerateIR *generateIR = new GenerateIR();
                generateIR->open(argv[i] + string(".IR"));
                generateIR->generateIR(stmts);
                generateIR->close();
            }
            if (opt_rename.size()) {
                for (size_t i = 0; i < stmts.size(); i++) {
                    shared_ptr<Stmt> stmt = stmts[i];
                    if (stmt && stmt->moduleDefStmt()) {
                        LexicalScope scope;
                        shared_ptr<Stmt> renamedStmt = stmt->rename(opt_rename, scope);
                        renamedStmt->prettyPrint(cout, 0);
                    }
                }
            }
            if (opt_inline) {
                Inliner *inliner = new Inliner();
                vector<shared_ptr<Stmt>> inlinedStmts = inliner->processPackage(stmts);
                for (size_t i = 0; i < inlinedStmts.size(); i++) {
                    inlinedStmts[i]->prettyPrint(cout, 0);
                }
            }
        }
    }
    return (numberOfSyntaxErrors == 0) ? 0 : 1;
}
