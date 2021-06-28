#include <string>

class Connectors {
  public:
    const static std::string AND = "AND";

    const static string OR = "OR";

    const static string NOT = "NOT";

    const static string IMPLIES = "=>";

    const static string BICOND = "<=>";

    static bool isAND(string connector) { return !AND.compare(connector); }

    static bool isOR(string connector) { return !OR.compare(connector); }

    static bool isNOT(string connector) { return !NOT.compare(connector); }

    static bool isIMPLIES(string connector) {
        return !IMPLIES.compare(connector);
    }

    static int isBICOND(string connector) {
        return !BICOND.compare(connector);
    }
};