#include <string>
#include <vector>
#include <memory>

class BSVType {
 public:
  const std::string name;
  const bool numeric;
  const bool isVar;
  std::vector<std::shared_ptr<BSVType>> params;
  
  BSVType(std::string name) : name(name), numeric(false), isVar(false) {
  }

  std::string to_string();

};
