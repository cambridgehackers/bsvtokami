#pragma once

#include <string>
#include <map>
#include <memory>
#include "BSVType.h"
#include "SourcePos.h"

using namespace std;

class Declaration;

class EnumDeclaration;

class EnumElementDeclaration;

class FunctionDefinition;

class InterfaceDeclaration;

class MethodDeclaration;

class MethodDefinition;

class ModuleDefinition;

class StructDeclaration;

class UnionDeclaration;

class TypeSynonymDeclaration;


enum BindingType {
    GlobalBindingType,
    ModuleParamBindingType,
    MethodParamBindingType,
    LocalBindingType
};

class DeclarationVisitor {
public:
    // called for all declarations
    virtual void visitDeclaration(const shared_ptr<Declaration> &declaration) {}
    virtual void visitEnumDeclaration(const shared_ptr<EnumDeclaration> &decl) {}
    virtual void visitFunctionDefinition(const shared_ptr<FunctionDefinition> &decl) {}
    virtual void visitInterfaceDeclaration(const shared_ptr<InterfaceDeclaration> &decl) {}
    virtual void visitMethodDefinition(const shared_ptr<MethodDefinition> &decl) {}
    virtual void visitMethodDeclaration(const shared_ptr<MethodDeclaration> &decl) {}
    virtual void visitModuleDefinition(const shared_ptr<ModuleDefinition> &decl) {}
    virtual void visitStructDeclaration(const shared_ptr<StructDeclaration> &decl) {}
    virtual void visitTypeSynonymDeclaration(const shared_ptr<TypeSynonymDeclaration> &decl) {}
    virtual void visitUnionDeclaration(const shared_ptr<UnionDeclaration> &decl) {}
};

class Declaration : public enable_shared_from_this<Declaration> {
public:
    const std::string package;
    const std::string name;
    const std::string uniqueName;
    const std::shared_ptr<BSVType> bsvtype;
    const BindingType bindingType;
    shared_ptr<Declaration> parent;
    const SourcePos sourcePos;

    Declaration(const std::string &name, std::shared_ptr<BSVType> bsvtype)
            : package(), name(name), uniqueName(genUniqueName(string(), name, LocalBindingType)), bsvtype(bsvtype), bindingType(LocalBindingType) {
        if (bsvtype) {
            for (int i = 0; i < bsvtype->params.size(); i++) {
                numericTypeParamVector.push_back(bsvtype->params[i]->isNumeric());
            }
        }
    };

    Declaration(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype, const BindingType bt = LocalBindingType)
    : package(package), name(name), uniqueName(genUniqueName(package, name, bt)), bsvtype(bsvtype), bindingType(bt) {
        if (bsvtype) {
            for (int i = 0; i < bsvtype->params.size(); i++) {
                numericTypeParamVector.push_back(bsvtype->params[i]->isNumeric());
            }
        }
    };

    virtual shared_ptr<EnumDeclaration> enumDeclaration() { return shared_ptr<EnumDeclaration>(); }
    virtual shared_ptr<FunctionDefinition> functionDefinition() { return shared_ptr<FunctionDefinition>(); }
    virtual shared_ptr<InterfaceDeclaration> interfaceDeclaration() { return shared_ptr<InterfaceDeclaration>(); }
    virtual shared_ptr<ModuleDefinition> moduleDefinition() { return shared_ptr<ModuleDefinition>(); }
    virtual shared_ptr<MethodDefinition> methodDefinition() { return shared_ptr<MethodDefinition>(); }
    virtual shared_ptr<MethodDeclaration> methodDeclaration() { return shared_ptr<MethodDeclaration>(); }
    virtual shared_ptr<StructDeclaration> structDeclaration() { return shared_ptr<StructDeclaration>(); }
    virtual shared_ptr<TypeSynonymDeclaration> typeSynonymDeclaration() { return shared_ptr<TypeSynonymDeclaration>(); }
    virtual shared_ptr<UnionDeclaration> unionDeclaration() { return shared_ptr<UnionDeclaration>(); }

    const vector<bool> numericTypeParams() {
        return numericTypeParamVector;
    }

    virtual ~Declaration() {}

private:
    vector<bool> numericTypeParamVector;
    static string genUniqueName(const string &package, const string &name, BindingType bt);
};

class EnumDeclaration : public Declaration {
public:
    std::vector<std::shared_ptr<Declaration> > members;

    EnumDeclaration(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype)
    : Declaration(package, name, bsvtype, GlobalBindingType) {};
    shared_ptr<EnumDeclaration> enumDeclaration() override { return static_pointer_cast<EnumDeclaration, Declaration>(shared_from_this()); }

};


class FunctionDefinition : public Declaration {
public:
    FunctionDefinition(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype, const BindingType bt = LocalBindingType) : Declaration(package, name, bsvtype, bt) {};
    shared_ptr<FunctionDefinition> functionDefinition() override { return static_pointer_cast<FunctionDefinition, Declaration>(shared_from_this()); }
};

class InterfaceDeclaration : public Declaration {
public:
    std::vector<std::shared_ptr<Declaration> > members;

    InterfaceDeclaration(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype)
    : Declaration(package, name, bsvtype, GlobalBindingType) {};
    shared_ptr<InterfaceDeclaration> interfaceDeclaration() override { return static_pointer_cast<InterfaceDeclaration, Declaration>(shared_from_this()); }

};

class MethodDeclaration : public Declaration {
public:
    MethodDeclaration(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype) : Declaration(package, name, bsvtype) {};
    shared_ptr<MethodDeclaration> methodDeclaration() override { return static_pointer_cast<MethodDeclaration, Declaration>(shared_from_this()); }

};

class MethodDefinition : public Declaration {
public:
    MethodDefinition(const std::string &name, std::shared_ptr<BSVType> bsvtype) : Declaration(string(), name, bsvtype) {};
    shared_ptr<MethodDefinition> methodDefinition() override { return static_pointer_cast<MethodDefinition, Declaration>(shared_from_this()); }

};

class ModuleDefinition : public Declaration {
public:
    ModuleDefinition(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype) : Declaration(package, name, bsvtype, GlobalBindingType) {};
    shared_ptr<ModuleDefinition> moduleDefinition() override { return static_pointer_cast<ModuleDefinition, Declaration>(shared_from_this()); }
};

class StructDeclaration : public Declaration {
public:
    std::vector<std::shared_ptr<Declaration> > members;

    StructDeclaration(const std::string &package, const std::string &name, std::shared_ptr<BSVType> bsvtype)
            : Declaration(package, name, bsvtype, GlobalBindingType) {};
    shared_ptr<StructDeclaration> structDeclaration() override { return static_pointer_cast<StructDeclaration, Declaration>(shared_from_this()); }
};

class TypeSynonymDeclaration : public Declaration {
public:
    const shared_ptr<BSVType> lhstype;
public:
    TypeSynonymDeclaration(const std::string &package, const std::string &name, std::shared_ptr<BSVType> lhstype, std::shared_ptr<BSVType> bsvtype)
    : Declaration(package, name, bsvtype, GlobalBindingType), lhstype(lhstype) {};
    shared_ptr<TypeSynonymDeclaration> typeSynonymDeclaration() override { return static_pointer_cast<TypeSynonymDeclaration, Declaration>(shared_from_this()); }

};

class UnionDeclaration : public Declaration {
public:
    std::vector<std::shared_ptr<Declaration> > members;

    UnionDeclaration(std::string name, std::shared_ptr<BSVType> bsvtype)
            : Declaration(package, name, bsvtype, GlobalBindingType) {};
    shared_ptr<UnionDeclaration> unionDeclaration() override { return static_pointer_cast<UnionDeclaration, Declaration>(shared_from_this()); }
    shared_ptr<Declaration> lookupMember(const string &memberName);
};