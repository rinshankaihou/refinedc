#pragma once

#include "fdsched/message.h"

struct callback {
  priority_t prio;
  int (*f)(struct message *msg);
};
