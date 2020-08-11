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
#include <string.h>
#include <sys/stat.h>

//#include <boost/filesystem.hpp>


#include "antlr4-runtime.h"
#include "AstWriter.h"
#include "BSVLexer.h"
#include "BSVParser.h"
#include "BSVPreprocessor.h"
#include "GenerateAst.h"
#include "GenerateKami.h"
#include "GenerateKoika.h"
#include "GenerateIR.h"
#include "Inliner.h"
#include "SimplifyAst.h"
#include "TypeChecker.h"

using namespace antlr4;
//namespace fs = boost::filesystem;

void usage(char *const argv[]) {
    fprintf(stderr, "Usage: %s [-t]\n", argv[0]);
    exit(-1);
}

struct BSVOptions {
    bool dumptree;
    bool opt_type_check;
    bool opt_ast;
    bool opt_kami;
    bool opt_koika;
    bool opt_ir;
    bool opt_inline;
    vector<string> includePath;
    vector<string> definitions;
};

int processBSVFile(const string &inputFileName, shared_ptr<TypeChecker> typeChecker, const BSVOptions options) {
    char buffer[4096];
    strncpy(buffer, inputFileName.c_str(), sizeof(buffer));
    string packageName(::basename(buffer));
    packageName = packageName.substr(0, packageName.size() - 4);
    cerr << "processBSVFile package " << packageName << " filename " << inputFileName << endl;
    BSVPreprocessor preprocessor(inputFileName);
    preprocessor.define(options.definitions);
    CommonTokenStream tokens((TokenSource *) &preprocessor);

    tokens.fill();

    BSVParser parser(&tokens);
    //parser.addErrorListener(&ConsoleErrorListener::INSTANCE);
    BSVParser::PackagedefContext *tree = parser.packagedef();
    int numberOfSyntaxErrors = parser.getNumberOfSyntaxErrors();
    if (options.dumptree) {
        std::cout << tree->toStringTree(&parser) << std::endl << std::endl;
    }
    if (options.opt_ast) {
        typeChecker->visit(tree);
        GenerateAst *generateAst = new GenerateAst(packageName, typeChecker);
        shared_ptr<PackageDefStmt> packageDef = generateAst->generateAst(tree);
        AstWriter astWriter;
        astWriter.visit(packageDef);
        astWriter.writeAst(string("kami/") + packageName + string(".ast"));
        vector<shared_ptr<Stmt>> stmts = packageDef->stmts;
        SimplifyAst *simplifier = new SimplifyAst(packageName);
        vector<shared_ptr<Stmt>> simplifiedStmts;
        simplifier->simplify(stmts, simplifiedStmts);
        stmts = simplifiedStmts;
        if (options.opt_kami) {
            ::mkdir("kami", 0755);

            string kamiFileName("kami/");
            char buffer[4096];
            kamiFileName += packageName;
            kamiFileName += string(".v");
            GenerateKami *generateKami = new GenerateKami();
            generateKami->open(kamiFileName);
            generateKami->generateStmts(stmts, 0);
            generateKami->close();
        }
        if (options.opt_koika) {
            ::mkdir("koika", 0775);

            string koikaFileName("koika/");
            char buffer[4096];
	    strncpy(buffer, inputFileName.c_str(), sizeof(buffer));
            koikaFileName += string(::basename(buffer));
            koikaFileName += string(".koika");

            GenerateKoika *generateKoika = new GenerateKoika();
            generateKoika->open(koikaFileName);
            generateKoika->generateStmts(stmts);
            generateKoika->close();
        }
        if (options.opt_ir) {
            GenerateIR *generateIR = new GenerateIR();
            generateIR->open("kami/" + packageName + string(".IR"));
            generateIR->generateIR(stmts);
            generateIR->close();
        }
        string opt_rename;
        if (opt_rename.size()) {
            for (size_t i = 0; i < stmts.size(); i++) {
                shared_ptr<Stmt> stmt = stmts[i];
                if (stmt && stmt->moduleDefStmt()) {
                    shared_ptr<LexicalScope> scope(make_shared<LexicalScope>("rename"));
                    shared_ptr<Stmt> renamedStmt = stmt->rename(opt_rename, scope);
                    //renamedStmt->prettyPrint(cout, 0);
                }
            }
        }
        if (options.opt_inline) {
            Inliner *inliner = new Inliner();
            vector<shared_ptr<Stmt>> inlinedStmts = inliner->processPackage(stmts);
            for (size_t i = 0; i < inlinedStmts.size(); i++) {
                //inlinedStmts[i]->prettyPrint(cout, 0);
            }
        }
    }
    return numberOfSyntaxErrors;
}

int main(int argc, char *const argv[]) {
    bool dumptokens = false;
    bool dumptree = false;
    size_t numberOfSyntaxErrors = 0;

    int ch;
    BSVOptions options;
    options.opt_type_check = 1; // mandatory -- used when generating AST
    options.opt_ast = 1;
    options.opt_kami = 0;
    options.opt_koika = 0;
    options.opt_ir = 0;
    options.opt_inline = 0;
    string opt_rename;

    while ((ch = getopt(argc, argv, "D:I:air:t")) != -1) {
        switch (ch) {
            case 'a':
                options.opt_ast = 1;
                break;
            case 'D':
                options.definitions.push_back(optarg);
                break;
            case 'i':
                options.opt_ir = 1;
                break;
            case 'k':
                options.opt_kami = 1;
                break;
            case 'K':
                options.opt_koika = 1;
                break;
            case 'I':
                cerr << "include " << optarg << endl;
                options.includePath.push_back(optarg);
                break;
            case 'r':
                opt_rename = string(optarg);
                break;
            case 't':
                options.opt_type_check = 1;
                break;
            default:
                usage(argv);
        }
    }

    map<string,string> visitedPackages;
    for (int i = optind; i < argc; i++) {
        string inputFileName(argv[i]);
        char buffer[4096];
	strncpy(buffer, inputFileName.c_str(), sizeof(buffer));
        string input_basename(::basename(buffer));
        long dotpos = input_basename.find_first_of('.');
        string packageName = input_basename.substr(0, dotpos);
        std::cerr << "Parsing file -1- " << inputFileName << " package " << packageName << std::endl;

        shared_ptr<TypeChecker> typeChecker = make_shared<TypeChecker>(packageName, options.includePath,
                                                                       options.definitions);
        numberOfSyntaxErrors += processBSVFile(inputFileName, typeChecker, options);
        visitedPackages[packageName] = inputFileName;

        if (0) {
            const vector<string> visitedPackageNames = typeChecker->visitedPackageNames();
            for (int j = 0; j < visitedPackageNames.size(); j++) {
                const string packageName = visitedPackageNames[j];
                if (packageName == string("Prelude"))
                    continue;

                if (visitedPackages.find(packageName) == visitedPackages.cend()) {
                    string packageFileName = typeChecker->searchIncludePath(packageName);
                    std::cerr << "Processing imported file -2- " << packageFileName << " package " << packageName << std::endl;
                    processBSVFile(packageFileName, typeChecker, options);
                } else {
                    cerr << "Already visited package " << packageName << endl;
                }
            }
        }
    }
    return (numberOfSyntaxErrors == 0) ? 0 : 1;
}
