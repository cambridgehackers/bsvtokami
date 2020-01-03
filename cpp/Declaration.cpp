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
