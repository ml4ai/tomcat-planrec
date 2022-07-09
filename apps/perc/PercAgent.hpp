#pragma once

#include "../../lib/kb.h"
#include "Agent.hpp"


class PercAgent : public Agent {
    KnowledgeBase kb;
    std::vector<int> medic_trapped_coord;
    std::vector<int> transporter_trapped_coord;
    std::vector<int> engineer_trapped_coord;
    void process(mqtt::const_message_ptr msg) override;

  public:
    PercAgent(std::string address);
};
