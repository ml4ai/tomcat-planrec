#pragma once

#include "kb.h"
#include "typedefs.h"
#include "Agent.hpp"
#include <sw/redis++/redis++.h>
using namespace sw::redis;


class PercAgent : public Agent {
    KnowledgeBase kb;
    Redis redis;
    Time initial_time;
    void process(mqtt::const_message_ptr msg) override;

  public:
    PercAgent(std::string address, std::string redis_address);
};
