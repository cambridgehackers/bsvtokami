#pragma once

#include <string>
#include <map>
#include <memory>
#include "BSVType.h"

using namespace std;

class Declaration;

class EnumDeclaration;

class EnumElementDeclaration;

class InterfaceDeclaration;

class MethodDeclaration;

class MethodDefinition;

class ModuleDeclaration;

class StructDeclaration;

class StructMemberDeclaration;

class UnionDeclaration;

class UnionMemberDeclaration;

class TypeSynonymDeclaration;


enum BindingType {
    GlobalBindingType,
    ModuleParamBindingType,
    MethodParamBindingType,
    LocalBindingType
};

class Declaration : public enable_shared_from_this<Declaration> {
public:
    const std::string name;
    const std::shared_ptr<BSVType> bsvtype;
    const BindingType bindingType;
    shared_ptr<Declaration> parent;

    Declaration(std::string name, std::shared_ptr<BSVType> bsvtype, const BindingType bt = LocalBindingType)
    : name(name), bsvtype(bsvtype), bindingType(bt) {
        if (bsvtype) {
            for (int i = 0; i < bsvtype->params.size(); i++) {
                numericTypeParamVector.push_back(bsvtype->params[i]->isNumeric());
            }
        }
    };

    virtual shared_ptr<InterfaceDeclaration> interfaceDeclaration() { return shared_ptr<InterfaceDeclaration>(); }
    virtual shared_ptr<MethodDeclaration> methodDeclaration() { return shared_ptr<MethodDeclaration>(); }
    virtual shared_ptr<MethodDefinition> methodDefinition() { return shared_ptr<MethodDefinition>(); }

    const vector<bool> numericTypeParams() {
        return numericTypeParamVector;
    }

    virtual ~Declaration() {}

private:
    vector<bool> numericTypeParamVector;
};

class EnumDeclaration : public Declaration {
public:
    std::vector<std::shared_ptr<EnumElementDeclaration> > tags;

    EnumDeclaration(std::string name, std::shared_ptr<BSVType> bsvtype)
    : Declaration(name, bsvtype, GlobalBindingType) {};
};

class InterfaceDeclaration : public Declaration {
public:
    std::vector<std::shared_ptr<Declaration> > members;

    InterfaceDeclaration(std::string name, std::shared_ptr<BSVType> bsvtype)
    : Declaration(name, bsvtype, GlobalBindingType) {};
    virtual shared_ptr<InterfaceDeclaration> interfaceDeclaration() { return static_pointer_cast<InterfaceDeclaration, Declaration>(shared_from_this()); }

};

class MethodDeclaration : public Declaration {
public:
    MethodDeclaration(std::string name, std::shared_ptr<BSVType> bsvtype) : Declaration(name, bsvtype) {};
    virtual shared_ptr<MethodDeclaration> methodDeclaration() override { return static_pointer_cast<MethodDeclaration, Declaration>(shared_from_this()); }

};

class MethodDefinition : public Declaration {
public:
    MethodDefinition(std::string name, std::shared_ptr<BSVType> bsvtype) : Declaration(name, bsvtype) {};
    virtual shared_ptr<MethodDefinition> methodDefinition() override { return static_pointer_cast<MethodDefinition, Declaration>(shared_from_this()); }

};

class ModuleDefinition : public Declaration {
public:
    ModuleDefinition(std::string name, std::shared_ptr<BSVType> bsvtype) : Declaration(name, bsvtype, GlobalBindingType) {};
    static shared_ptr<ModuleDefinition> create(std::string name, std::shared_ptr<BSVType> bsvtype) {
        return shared_ptr<ModuleDefinition>(new ModuleDefinition(name, bsvtype));
    }
};

class TypeSynonymDeclaration : public Declaration {
public:
    const shared_ptr<BSVType> typedeftype;
public:
    TypeSynonymDeclaration(std::string name, std::shared_ptr<BSVType> bsvtype, std::shared_ptr<BSVType> typedeftype)
    : Declaration(name, bsvtype, GlobalBindingType), typedeftype(typedeftype) {};
};