#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stddef.h>
#include <stdatomic.h>

//@rc::import spinlock_annot from refinedc.examples.spinlock (for code only)
//@rc::import spinlock_def from refinedc.examples.spinlock
//@rc::context `{!lockG Σ}

struct spinlock {
    atomic_bool lock;
};

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_spinlock>>")]]
[[rc::exists("gamma : lock_id")]]
[[rc::ensures("p @ &own<spinlock<gamma>>")]]
void sl_init(struct spinlock* lock);


[[rc::parameters("p : loc", "gamma : lock_id", "beta : own_state")]]
[[rc::args("p @ &frac<beta, spinlock<gamma>>")]]
[[rc::ensures("p @ &frac<beta, spinlock<gamma>>", "[spinlock_token gamma []]")]]
void sl_lock(struct spinlock* lock);


[[rc::parameters("p : loc", "gamma : lock_id", "beta : own_state")]]
[[rc::args("p @ &frac<beta, spinlock<gamma>>")]]
[[rc::requires("[spinlock_token gamma []]")]]
[[rc::ensures("p @ &frac<beta, spinlock<gamma>>")]]
[[rc::annot_args("0 : 1 LockA")]]
void sl_unlock(struct spinlock* lock);

#endif
