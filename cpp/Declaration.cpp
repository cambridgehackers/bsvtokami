//
// Created by Jamey Hicks on 1/1/20.
//

#include "Declaration.h"

string Declaration::genUniqueName(const string &name, BindingType bt) {
    static long uniqifier = 0;
    if (bt == GlobalBindingType)
        return name;
    else
        return name + "-" + ::to_string(uniqifier++);
}

shared_ptr<Declaration> UnionDeclaration::lookupMember(const string &memberName) {
    for (int i = 0; i < members.size(); i++) {
        if (members[i]->name == memberName)
            return members[i];
    }
    return shared_ptr<Declaration>();
}
