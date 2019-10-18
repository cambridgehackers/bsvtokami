//
// Created by Jamey Hicks on 10/15/19.
//

#include <stdio.h>
#include "antlr4-runtime.h"
#include "BSVLexer.h"
#include "BSVPreprocessor.h"

BSVPreprocessor::BSVPreprocessor(string inputFileName) {
    shared_ptr<ANTLRFileStream> inputStream(new ANTLRFileStream(inputFileName));
    shared_ptr<BSVLexer> lexer(new BSVLexer(inputStream.get()));
    inputStreams.push_back(inputStream);
    tokenSources.push_back(lexer);
    condStack.push_back(true);
    validStack.push_back(true);
}

BSVPreprocessor::~BSVPreprocessor() {}

unique_ptr<Token> BSVPreprocessor::nextToken() {
    while (1) {
        unique_ptr<Token> token = tokenSources.back()->nextToken();
        if (token->getChannel() == 2) {
            string text = token->getText();
            if (text == "`ifdef" || text == "`ifndef") {
                // consume one
                token = tokenSources.back()->nextToken();
                //fprintf(stderr, "%s %s\n", text.c_str(), token->getText().c_str());
                bool key_defined = true; //FIXME
                condStack.push_back(key_defined);
                if (text == ("`ifdef"))
                    validStack.push_back(condStack.back() && validStack.back());
                else
                    validStack.push_back(!condStack.back() && validStack.back());
            } else if (text == "`else") {
                bool topcond = condStack.back();
                condStack.pop_back();
                condStack.push_back(!topcond);
                validStack.pop_back();
                validStack.push_back(condStack.back() && validStack.back());
            } else if (text == "`endif") {
                condStack.pop_back();
                validStack.pop_back();
            } else if (text == "`include") {
                token = tokenSources.back()->nextToken();
                string include = token->getText();
                if (!validStack.back())
                    continue;
                string filename = findIncludeFile(include);

            } else {
                fprintf(stderr, "Unhandled preprocessor token %s\n", text.c_str());
            }
            continue;
        } else if (!validStack.back()) {
            continue;
        } else {
            return token;
        }
    }
}

size_t BSVPreprocessor::getLine() const {
    return tokenSources.back()->getLine();
}

size_t BSVPreprocessor::getCharPositionInLine() {
    return tokenSources.back()->getCharPositionInLine();
}

CharStream *BSVPreprocessor::getInputStream() {
    return tokenSources.back()->getInputStream();
}

string BSVPreprocessor::getSourceName() {
    return tokenSources.back()->getSourceName();
}

Ref<TokenFactory<CommonToken>> BSVPreprocessor::getTokenFactory() {
    return tokenSources.back()->getTokenFactory();
}

string BSVPreprocessor::findIncludeFile(string include) {
    string filename = include.substr(1, include.size() - 2);
    fprintf(stderr, "`include %s\n", filename.c_str());

    //FIXME search path
    return filename;
}
