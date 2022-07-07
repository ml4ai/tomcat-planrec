#pragma once

#include "../../lib/kb.h"
#include "Agent.hpp"

class PercAgent : public Agent {
    KnowledgeBase kb;
    void process(mqtt::const_message_ptr msg) override;

  public:
    PercAgent(std::string address);
};
