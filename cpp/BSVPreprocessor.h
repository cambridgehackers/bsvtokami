//
// Created by Jamey Hicks on 10/15/19.
//

#pragma once
#include <TokenStream.h>
#include <map>
#include <memory>
#include <vector>

#include "BSVLexer.h"

using namespace antlr4;
using namespace std;

class BSVPreprocessor : public TokenSource {
    vector<shared_ptr<ANTLRInputStream>> inputStreams;
    vector<shared_ptr<BSVLexer>> tokenSources;
    vector<bool> condStack;
    vector<bool> validStack;
    map<string,string> defines;

public:
    BSVPreprocessor(string inputFileName);
    ~BSVPreprocessor();

    void define(const vector<string> &definitions);
    void define(const string &varname);
    void define(const string &varname, const string &varval);

    unique_ptr<Token> nextToken() override;

    size_t getLine() const override;

    size_t getCharPositionInLine() override;

    CharStream *getInputStream() override;

    string getSourceName() override;

    Ref<TokenFactory<CommonToken>> getTokenFactory() override;

    string findIncludeFile(string basicString);
};


