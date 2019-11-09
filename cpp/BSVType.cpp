
#include <strstream>
#include <iostream>

#include "BSVType.h"

using namespace std;

int BSVType::gen = 0;
string BSVType::newName() {
    int number = BSVType::gen++;
    char buf[128];
    snprintf(buf, sizeof(buf), "type%d", number);
    return string(buf);
}

std::string BSVType::to_string() {
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

void BSVType::prettyPrint(ostream &out, int depth) {
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
