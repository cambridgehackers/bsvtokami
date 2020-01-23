//
// Created by Jamey Hicks on 1/14/20.
//

#include <string>

#include "AttributeInstanceVisitor.h"

using namespace std;

AttributeInstanceVisitor::AttributeInstanceVisitor() {

}

AttributeInstanceVisitor::~AttributeInstanceVisitor() {

}

antlrcpp::Any AttributeInstanceVisitor::visitPackagestmt(BSVParser::PackagestmtContext *ctx) {
    return visitChildren(ctx);
}

antlrcpp::Any AttributeInstanceVisitor::visitModuledef(BSVParser::ModuledefContext *ctx) {
    vector<string> attributes;
    for (int i = 0; ctx->attributeinstance(i); i++) {
        vector<string> attrspecs = visit(ctx->attributeinstance(i));
        for (int j = 0; j < attrspecs.size(); j++)
            attributes.push_back(attrspecs[j]);
    }
    return attributes;
}

antlrcpp::Any AttributeInstanceVisitor::visitFunctiondef(BSVParser::FunctiondefContext *ctx) {
    vector<string> attributes;
    for (int i = 0; ctx->attributeinstance(i); i++) {
        vector<string> attrspecs = visit(ctx->attributeinstance(i));
        for (int j = 0; j < attrspecs.size(); j++)
            attributes.push_back(attrspecs[j]);
    }
    return attributes;
}

antlrcpp::Any AttributeInstanceVisitor::visitVarbinding(BSVParser::VarbindingContext *ctx) {
    vector<string> attributes;
    for (int i = 0; ctx->attributeinstance(i); i++) {
        vector<string> attrspecs = visit(ctx->attributeinstance(i));
        for (int j = 0; j < attrspecs.size(); j++)
            attributes.push_back(attrspecs[j]);
    }
    return attributes;
}

antlrcpp::Any AttributeInstanceVisitor::visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) {
    vector<string> attributes;
    for (int i = 0; ctx->attrspec(i); i++) {
        string attr = visit(ctx->attrspec(i));
        attributes.push_back(attr);
    }
    return attributes;
}

antlrcpp::Any AttributeInstanceVisitor::defaultResult() {
    vector<string> attributes;
    return attributes;
}

antlrcpp::Any AttributeInstanceVisitor::aggregateResult(antlrcpp::Any any, const antlrcpp::Any &nextResult) {
    vector<string> attributes = any;
    antlrcpp::Any any2 = nextResult;
    const vector<string> nextAttributes = any2;
    for (int i = 0; i < nextAttributes.size(); i++) {
        attributes.push_back(nextAttributes[i]);
    }

    return attributes;
}

bool AttributeInstanceVisitor::contains(antlrcpp::Any any, std::string key) {
    vector<string> attributes = any;
    for (int i = 0; i < attributes.size(); i++) {
        if (attributes[i] == key)
            return true;
    }
    return false;
}

antlrcpp::Any AttributeInstanceVisitor::visitAttrspec(BSVParser::AttrspecContext *ctx) {
    //FIXME: return a tuple
    return ctx->getText();
}

string AttributeInstanceVisitor::sourceLocation(antlr4::ParserRuleContext *ctx) {
    antlr4::Token *start = ctx->getStart();
    string filename = start->getTokenSource()->getSourceName();
    size_t line = start->getLine();
    return filename + ":" + to_string(line);
}