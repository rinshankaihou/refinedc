#include <stdbool.h>
#include "latch.h"

void latch_wait(struct latch* latch) {
  while(atomic_load(&latch->released) == (_Bool)false) {}
}

void latch_release(struct latch* latch) {
  atomic_store(&latch->released, true);
}
