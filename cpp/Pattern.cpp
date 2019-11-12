//
// Created by Jamey Hicks on 11/11/19.
//

#include "Pattern.h"

void IntPattern::prettyPrint(ostream &out, int depth, int precedence) {
    out << value;
}

void TaggedPattern::prettyPrint(ostream &out, int depth, int precedence) {
    out << "tagged " << value;
}

void TuplePattern::prettyPrint(ostream &out, int depth, int precedence) {
    out << "{";
    for (int i = 0; i < subpatterns.size(); i++) {
        if (i > 0)
            out << ", ";
        subpatterns[i]->prettyPrint(out, depth, precedence);
    }
    out << "} ";
}

void VarPattern::prettyPrint(ostream &out, int depth, int precedence) {
    out << "." << value;
}

void WildcardPattern::prettyPrint(ostream &out, int depth, int precedence) {
    out << ".*";
}