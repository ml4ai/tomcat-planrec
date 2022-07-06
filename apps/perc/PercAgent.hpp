#pragma once

#include "Agent.hpp"

class PercAgent : public Agent {
    void process(mqtt::const_message_ptr msg) override;

  public:
    PercAgent(std::string address);
};
