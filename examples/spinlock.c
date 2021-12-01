#include <stdbool.h>
#include <spinlock.h>

//@rc::import spinlock_proof from refinedc.examples.spinlock (for proofs only)

 [[rc::manual_proof("refinedc.examples.spinlock:spinlock_proof, type_sl_init")]]
void sl_init(struct spinlock* lock) {
   lock->lock = 0;
}

void sl_lock(struct spinlock* lock) {
  bool expected = 0;
  [[rc::inv_vars("expected : false @ builtin_boolean")]]
  while(atomic_compare_exchange_strong(&lock->lock, &expected, 1) == (bool)false) {
    expected = 0;
  }
}


void sl_unlock(struct spinlock* lock) {
  atomic_store(&lock->lock, 0);
}

// Original version from Hafnium (locks must come from the same allocation).
void sl_lock_both_same_prov(struct spinlock* a, struct spinlock* b) {
  if (a < b) {
		sl_lock(a);
		sl_lock(b);
	} else {
		sl_lock(b);
		sl_lock(a);
	}
}

// More general version allowing locks from different allocations.
void sl_lock_both(struct spinlock* a, struct spinlock* b) {
  if ((uintptr_t) a < (uintptr_t) b) {
		sl_lock(a);
		sl_lock(b);
	} else {
		sl_lock(b);
		sl_lock(a);
	}
}


