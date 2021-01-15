#ifndef LATCH_H
#define LATCH_H

#include <stddef.h>
#include <stdbool.h>
#include <stdatomic.h>

//@rc::import latch_def from refinedc.examples.latch
//@rc::require refinedc.examples.latch

struct latch {
    atomic_bool released;
};

#define LATCH_INIT ((struct latch){.released = false})

[[rc::parameters("p : loc", "beta : own_state", "P : {iProp Σ}")]]
[[rc::args("p @ &frac<beta, latch<P>>")]]
[[rc::ensures("frac beta p : latch<P>", "[P]")]]
void latch_wait(struct latch* latch);

[[rc::parameters("p : loc", "beta : own_state", "P : {iProp Σ}")]]
[[rc::args("p @ &frac<beta, latch<P>>")]]
[[rc::requires("[□ P]")]]
[[rc::ensures("frac beta p : latch<P>")]]
void latch_release(struct latch* latch);

#endif
