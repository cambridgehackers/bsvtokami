#pragma once

#include <iostream>
#include <string>
#include <vector>
#include <memory>

using namespace std;

enum BSVTypeKind {
    BSVType_Invalid,
    BSVType_Symbolic,
    BSVType_Numeric
};
class BSVType : public enable_shared_from_this<BSVType> {
private:
    static int gen;

    static std::string newName();

public:
    const std::string name;
    const BSVTypeKind kind;
    const bool isVar;
    std::vector<std::shared_ptr<BSVType>> params;

    static BSVTypeKind kindFromName(const string &name);

    BSVType() : name(newName()), kind(BSVType_Symbolic), isVar(true) {}
    BSVType(std::string name, BSVTypeKind kind, bool isVar,
            const std::vector<std::shared_ptr<BSVType>> &params)
            : name(name), kind(kind), isVar(isVar), params(params) {}

    BSVType(std::string name, BSVTypeKind kind = BSVType_Invalid, bool isVar = false)
        : name(name), kind(kind == BSVType_Invalid ? kindFromName(name) : kind), isVar(isVar) {
    }

    BSVType(std::string name, const std::vector<std::shared_ptr<BSVType>> &params) : name(name), kind(kindFromName(name)),
                                                                                     isVar(false), params(params) {}

    BSVType(std::string name, const std::shared_ptr<BSVType> &param0) : name(name), kind(kindFromName(name)),
                                                                        isVar(false), params({param0}) {}

    std::string to_string() const;

    bool isNumeric() const { return kind == BSVType_Numeric; }

    bool isConstant() const;
    long numericValue() const;

    virtual void prettyPrint(ostream &out, int depth = 0) const;

    static shared_ptr<BSVType> create() {
        return shared_ptr<BSVType>(new BSVType());
    }

    static shared_ptr<BSVType> create(std::string name, BSVTypeKind kind = BSVType_Symbolic, bool isVar = false) {
        return shared_ptr<BSVType>(new BSVType(name, kind, isVar));
    }

    static shared_ptr<BSVType> create(std::string name, const std::vector<std::shared_ptr<BSVType>> &params) {
        return shared_ptr<BSVType>(new BSVType(name, params));
    }

    static shared_ptr<BSVType> create(std::string name, const std::shared_ptr<BSVType> &param0) {
        vector<shared_ptr<BSVType>> params;
        params.push_back(param0);
        return make_shared<BSVType>(name, params);
    }

    static shared_ptr<BSVType> create(std::string name,
                                      const std::shared_ptr<BSVType> &param0,
                                      const std::shared_ptr<BSVType> &param1) {
        vector<shared_ptr<BSVType>> params;
        params.push_back(param0);
        params.push_back(param1);
        return make_shared<BSVType>(name, params);
    }

    shared_ptr<BSVType> eval() const;
};