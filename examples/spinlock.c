#include <stdbool.h>
#include <spinlock.h>

//@rc::import spinlock_proof from refinedc.examples.spinlock (for proofs only)

 [[rc::manual_proof("refinedc.examples.spinlock:spinlock_proof, type_sl_init")]]
void sl_init(struct spinlock* lock) {
   lock->lock = 0;
}

void sl_lock(struct spinlock* lock) {
  bool expected = 0;
  [[rc::inv_vars("expected : false @ boolean<bool_it>")]]
  while(atomic_compare_exchange_strong(&lock->lock, &expected, 1) == (bool)false) {
    expected = 0;
  }
}


void sl_unlock(struct spinlock* lock) {
  atomic_store(&lock->lock, 0);
}

void sl_lock_both(struct spinlock* a, struct spinlock* b) {
  if ((uintptr_t)a < (uintptr_t)b) {
		sl_lock(a);
		sl_lock(b);
	} else {
		sl_lock(b);
		sl_lock(a);
	}
}
