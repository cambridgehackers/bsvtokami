//
// Created by Jamey Hicks on 8/11/20.
//

#include <iostream>
#include <fstream>

#include "AstWriter.h"

AstWriter::AstWriter() {}
AstWriter::~AstWriter() noexcept {}

void AstWriter::visitModuleDef(const shared_ptr<ModuleDefStmt> &moduledef) {
    bsvproto::ModuleDefStmt moduledef_proto;
    moduledef_proto.set_name(moduledef->name);
    bsvproto::Stmt *stmt = packagedef.add_stmt();
    *stmt->mutable_moduledefstmt() = moduledef_proto;
}

bool AstWriter::writeAst(std::string filename) {
    ofstream output(filename, ios::out | ios::trunc | ios::binary);
    packagedef.SerializeToOstream(&output);
    output.close();
    return true;
}
