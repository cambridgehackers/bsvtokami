#pragma once

#include <iostream>
#include <string>
#include <vector>
#include <memory>

using namespace std;

class BSVType {
private:
    static int gen;
    static std::string newName();
public:
    const std::string name;
    const bool numeric;
    const bool isVar;
    std::vector<std::shared_ptr<BSVType>> params;

    BSVType() : name(newName()), numeric(false), isVar(true) {}

    BSVType(std::string name, bool numeric = false, bool isVar = false) : name(name), numeric(numeric), isVar(isVar) {
    }

    BSVType(std::string name, const std::vector<std::shared_ptr<BSVType>> &params) : name(name), numeric(false), isVar(false), params(params) {
    }
    std::string to_string();
    virtual void prettyPrint(ostream &out, int depth = 0);
};
