#include "cpphop.h"

// Operators

// reserve truck
template <class State> std::optional<State> reserve(State state, Args args) {
    auto t = args["t"];
    if (state.t_res[t] == "n") {
        state.t_res[t] = "y";
        return state;
    }
    else {
        return std::nullopt;
    }
}

// move truck
template <class State> std::optional<State> move(State state, Args args) {
    auto t = args["t"];
    auto x = args["x"];
    auto y = args["y"];
    if (state.t_loc[t] == x) {
        state.t_loc[t] = y;
        if (state.t_load[t] != "e")
            state.p_loc[state.t_load[t]] = y;
        return state;
    }
    else {
        return std::nullopt;
    }
}

// load truck
template <class State> std::optional<State> load(State state, Args args) {
    auto t = args["t"];
    auto p = args["p"];
    if (state.t_load[t] == "e") {
        state.t_load[t] = p;
        return state;
    }
    else {
        return std::nullopt;
    }
}

// free truck
template <class State> std::optional<State> free(State state, Args args) {
    auto t = args["t"];
    if (state.t_res[t] == "y") {
        state.t_res[t] = "n";
        return state;
    }
    else {
        return std::nullopt;
    }
}

// Methods
// dispatch truck
template <class State> pTasks dispatch(State state, Args args) {
    auto t = args["t"];
    auto x = args["x"];

    return {1, {Task("reserve", Args({{"t", t}}), {"t"},{t}),
                Task("move", Args({{"t", t}, {"x", "home"}, {"y", x}}), {"t", "x", "y"},{t})}};

}

// return truck
template <class State> pTasks return_t(State state, Args args) {
    auto t = args["t"];
    auto x = args["x"];
    auto y = args["y"];

    return {1, {Task("move", Args({{"t", t}, {"x", x}, {"y", "home"}}), {"t", "x", "y"},{t}),
            Task("free", Args({{"t", t}}), {"t"},{t})}};

}

// transport
template <class State> pTasks transport(State state, Args args) {
    auto p = args["p"];
    auto t = args["t"];
    auto x = args["x"];
    auto y = args["y"];

    if (state.p_loc[p] == x and x != y)
        return {1, {Task("dispatch", Args({{"t", t}, {"x", x}}), {"t", "x"}, {t}),
                    Task("load", Args({{"t", t}, {"p", p}}), {"t", "p"}, {t, p}),
                    Task("move", Args({{"t", t}, {"x", x}, {"y", y}}), {"t", "x", "y"}, {t}),
                    Task("return_t", Args({{"t", t}, {"x", y}, {"y", "home"}}), {"t", "x", "y"}, {t})}};
                }

class TransState {
  public:
    TransState() = default;
    TransState(std::string name) : name(name){};
    std::string name;
    std::unordered_map<std::string, std::string> t_loc;
    std::unordered_map<std::string, std::string> p_loc;
    std::unordered_map<std::string, std::string> t_res;
    std::unordered_map<std::string, std::string> t_load;
};

class TransSelector {


};

class TransDomain {
  public:
    // Declare operators
    Operators<TransState> operators =
        Operators<TransState>({{"reserve", reserve},
                                {"move", move},
                                {"load", load},
                                {"free", free}});

    // Declare methods
    Methods<TransState> methods = Methods<TransState>({
        {"dispatch", {dispatch}},
        {"return_t", {return_t}},
        {"transport", {transport}},
    });

    TransDomain() {
        std::cout << "Operators: ";
        print(this->operators);

        std::cout << "Methods: ";
        print(this->methods);
    };
};
