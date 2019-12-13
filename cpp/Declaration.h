#pragma once

#include <string>
#include <map>
#include <memory>
#include "BSVType.h"

class Declaration;

class EnumDeclaration;

class EnumElementDeclaration;

class MethodDeclaration;

class ModuleDeclaration;

class StructDeclaration;

class StructMemberDeclaration;

class UnionDeclaration;

class UnionMemberDeclaration;


enum BindingType {
    GlobalBindingType,
    ModuleParamBindingType,
    MethodParamBindingTYpe,
    LocalBindingType
};

class Declaration {
public:
    const std::string name;
    const std::shared_ptr<BSVType> bsvtype;
    const BindingType bindingType;

    Declaration(std::string name, std::shared_ptr<BSVType> bsvtype, const BindingType bt = LocalBindingType)
    : name(name), bsvtype(bsvtype), bindingType(bt) {};

    virtual ~Declaration() {}
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
};

class MethodDeclaration : public Declaration {
public:
    MethodDeclaration(std::string name, std::shared_ptr<BSVType> bsvtype) : Declaration(name, bsvtype) {};
    static shared_ptr<MethodDeclaration> create(std::string name, std::shared_ptr<BSVType> bsvtype) {
        return shared_ptr<MethodDeclaration>(new MethodDeclaration(name, bsvtype));
    }
};

class MethodDefinition : public Declaration {
public:
    MethodDefinition(std::string name, std::shared_ptr<BSVType> bsvtype) : Declaration(name, bsvtype) {};
    static shared_ptr<MethodDefinition> create(std::string name, std::shared_ptr<BSVType> bsvtype) {
        return shared_ptr<MethodDefinition>(new MethodDefinition(name, bsvtype));
    }
};

class ModuleDefinition : public Declaration {
public:
    ModuleDefinition(std::string name, std::shared_ptr<BSVType> bsvtype) : Declaration(name, bsvtype) {};
    static shared_ptr<ModuleDefinition> create(std::string name, std::shared_ptr<BSVType> bsvtype) {
        return shared_ptr<ModuleDefinition>(new ModuleDefinition(name, bsvtype));
    }
};