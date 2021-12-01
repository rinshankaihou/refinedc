#ifndef LATCH_H
#define LATCH_H

#include <stddef.h>
#include <stdbool.h>
#include <stdatomic.h>

struct [[rc::refined_by("P : {iProp Σ}")]] latch {
    [[rc::field("atomic_bool<u8, {(□ P)}, True>")]]
    atomic_bool released;
};

#define LATCH_INIT ((struct latch){.released = false})

[[rc::parameters("p : loc", "beta : own_state", "P : {iProp Σ}")]]
[[rc::args("p @ &frac<beta, P @ latch>")]]
[[rc::ensures("frac beta p : P @ latch", "[P]")]]
void latch_wait(struct latch* latch);

[[rc::parameters("p : loc", "beta : own_state", "P : {iProp Σ}")]]
[[rc::args("p @ &frac<beta, P @ latch>")]]
[[rc::requires("[□ P]")]]
[[rc::ensures("frac beta p : P @ latch")]]
void latch_release(struct latch* latch);

#endif
