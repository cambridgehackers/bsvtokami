#include <assert.h>
#include <iostream>
#include <map>
#include <set>
#include <strstream>
#include <math.h>

#include "BSVType.h"

using namespace std;

int BSVType::gen = 0;
string BSVType::newName() {
    int number = BSVType::gen++;
    char buf[128];
    snprintf(buf, sizeof(buf), "type%d", number);
    return string(buf);
}

BSVTypeKind BSVType::kindFromName(const string &name) {
    static const string digits = "0123456789";
    if (name.find_first_not_of(digits) == string::npos) {
        return BSVType_Numeric;
    } else if (name == "TLog"
               || name == "TDiv"
               || name == "TMul"
               || name == "TAdd"
               || name == "TSub") {
        return BSVType_Numeric;
    } else {
        return BSVType_Symbolic;
    }
}

std::string BSVType::to_string() const {
    std::string result(name);
    if (params.size()) {
        result += "#(";
        for (size_t i = 0; i < params.size(); i++) {
            if (i)
                result += ",";
            result += params[i]->to_string();
        }
        result += ")";
    }
    return result;
}

bool BSVType::isConstant() const {
    bool isConstant = !isVar;
    for (int i = 0; i < params.size(); i++) {
        isConstant &= params[i]->isConstant();
    }
    return isConstant;
}

shared_ptr<BSVType> BSVType::eval() const {
    if (!isConstant())
        return make_shared<BSVType>(name, kind, isVar, params);
    long value = 0;
    if ("TLog" == name) {
        value = ceil(log2((double) params[0]->numericValue()));
    } else if ("TDiv" == name) {
        value = ceil(params[0]->numericValue() / params[1]->numericValue());
    } else if ("TMul" == name) {
        value = params[0]->numericValue() * params[1]->numericValue();
    } else {
        return make_shared<BSVType>(name, kind, isVar, params);
    }
    return make_shared<BSVType>(::to_string(value), BSVType_Numeric);
}

long BSVType::numericValue() const {
    static const string digits = "0123456789";
    if (name.find_first_not_of(digits) == string::npos) {
        return stol(name);
    } else {
        assert(0);
        return -22;
    }
}

void BSVType::prettyPrint(ostream &out, int depth) const {
    out << name;
    if (params.size()) {
        out << "#(";
        for (size_t i = 0; i < params.size(); i++) {
            if (i > 0)
                out << ", ";
            params.at(i)->prettyPrint(out, 0);
        }
        out << ")";
    }
}

set<string> BSVType::freeVars() const {
    set<string> result;
    computeFreeVars(result);
    return result;
}

void BSVType::computeFreeVars(set<string> &mapping) const {
    if (isVar) {
        auto it = mapping.find(name);
        if (it == mapping.cend()) {
            mapping.insert(name);
        }
    }
    for (int i = 0; i < params.size(); i++) {
        params[i]->computeFreeVars(mapping);
    }
}
