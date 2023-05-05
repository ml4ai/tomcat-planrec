#pragma once

#include "kb.h"
#include "typedefs.h"
#include "Agent.hpp"
#include "Redis_Connect.h"


class PercAgent : public Agent {
    KnowledgeBase kb;
    Redis_Connect* rc;
    Time initial_time;
    bool start = false;
    std::string medic_current_loc = "sga";
    std::string engineer_current_loc = "sga";
    std::string transporter_current_loc = "sga";
    std::unordered_set<int> engineer_assist;
    std::unordered_set<int> transporter_assist;
    void process(mqtt::const_message_ptr msg) override;

  public:
    PercAgent(std::string address,std::string const& redis_address);
};
