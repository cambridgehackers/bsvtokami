//
// Created by Jamey Hicks on 8/11/20.
//

#pragma once

#include <string>
#include "AstVisitor.h"
#include "source_pos.pb.h"
#include "expr.pb.h"
#include "pattern.pb.h"
#include "lvalue.pb.h"
#include "stmt.pb.h"

class AstWriter : public AstVisitor {
private:
    bsvproto::PackageDef packagedef;
public:
    AstWriter();
    virtual ~AstWriter();

    bool writeAst(std::string filename);

    void visitModuleDef(const shared_ptr<ModuleDefStmt> &sharedPtr) override;

};
