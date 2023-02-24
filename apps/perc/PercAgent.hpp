#pragma once

#include "kb.h"
#include "typedefs.h"
#include "Agent.hpp"
#include "Redis_Connect.h"


class PercAgent : public Agent {
    KnowledgeBase kb;
    Redis_Connect* rc;
    Time initial_time;
    void process(mqtt::const_message_ptr msg) override;

  public:
    PercAgent(std::string address,std::string redis_address);
};
