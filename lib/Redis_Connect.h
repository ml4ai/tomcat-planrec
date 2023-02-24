#include <sw/redis++/redis++.h>
using namespace sw::redis;

class Redis_Connect {
  private:
    static Redis_Connect* instancePtr;

    Redis_Connect (std::string address = "tcp://127.0.0.1:6379") {
      this->redis = Redis(address);
    }

  public:
    Redis redis = Redis("tcp://127.0.0.1:6379");
    Redis_Connect (const Redis_Connect& obj)
      = delete;

    static Redis_Connect* getInstance(std::string address = "tcp://127.0.0.1:6379") {
      if (instancePtr == NULL) {
        instancePtr = new Redis_Connect(address);
        return instancePtr;
      }
      else {
        return instancePtr;
      }
    }
};

Redis_Connect *Redis_Connect::instancePtr = NULL;
