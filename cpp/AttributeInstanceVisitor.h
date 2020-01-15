//
// Created by Jamey Hicks on 1/14/20.
//

#ifndef BSV_PARSER_ATTRIBUTEINSTANCEVISITOR_H
#define BSV_PARSER_ATTRIBUTEINSTANCEVISITOR_H

#include <string>

#include <BSVBaseVisitor.h>

class AttributeInstanceVisitor : public BSVBaseVisitor {
public:
    AttributeInstanceVisitor();

    virtual ~AttributeInstanceVisitor();

    antlrcpp::Any visitPackagestmt(BSVParser::PackagestmtContext *ctx) override;

    antlrcpp::Any visitModuledef(BSVParser::ModuledefContext *ctx) override;

    antlrcpp::Any visitFunctiondef(BSVParser::FunctiondefContext *ctx) override;

    antlrcpp::Any visitVarbinding(BSVParser::VarbindingContext *ctx) override;

    antlrcpp::Any visitAttributeinstance(BSVParser::AttributeinstanceContext *ctx) override;

    bool contains(antlrcpp::Any attributes, std::string key);

    antlrcpp::Any visitAttrspec(BSVParser::AttrspecContext *ctx) override;

protected:
    antlrcpp::Any defaultResult() override;

    antlrcpp::Any aggregateResult(antlrcpp::Any any, const antlrcpp::Any &nextResult) override;

    std::string sourceLocation(antlr4::ParserRuleContext *ctx);

};


#endif //BSV_PARSER_ATTRIBUTEINSTANCEVISITOR_H
