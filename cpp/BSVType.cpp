
#include <strstream>

#include "BSVType.h"

std::string BSVType::to_string()
{
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
