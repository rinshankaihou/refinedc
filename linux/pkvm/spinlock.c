/* SPDX-License-Identifier: GPL-2.0-only */

#include <limits.h>
#include <stdbool.h>
#include <stdatomic.h>
#include <nvhe/spinlock.h>

// Ticket lock implementations generally (implicitly) assume that there are no
// more threads waiting for the lock than there are tickets to give. So in our
// case that would mean that the number of waiting threads is bounded by 2^16.
// This may perfectly be a resonable assumption, but formally working under it
// may not be so easy.
//
// Here we modify the ticket lock so that when 2^16-1 tickets have been given,
// the waiting threads have to wait until *all* the threads that have a ticket
// already are done. The last of the lucky threads resets the ticket dispenser
// so that all the threads stuck waiting can take a ticket.

#define NO_TICKET    (USHRT_MAX)
#define LAST_TICKET  ((USHRT_MAX - 1))

[[rc::manual_proof("refinedc.linux.pkvm.spinlock:spinlock_proof, "
                   "type_hyp_spin_lock_init")]]
static inline void hyp_spin_lock_init(hyp_spinlock_t *lock){
  // Set both the owner and the next ticket to 0 at once.
  lock->owner = 0;
  lock->next = 0;
}

[[rc::manual_proof("refinedc.linux.pkvm.spinlock:spinlock_proof, "
                   "type_hyp_spin_lock")]]
static inline void hyp_spin_lock(hyp_spinlock_t *lock){
  bool got_it;
  u16 ticket, next;

  // Get a ticket.
  do {
    // Take a ticket, or wait until the tickets are reset.
    do {
      ticket = lock->next;
    } while(ticket == NO_TICKET);

    // Check that the ticket is yours.
    next = ticket + 1;
    got_it = atomic_compare_exchange_strong(&lock->next, &ticket, next);
  } while(!got_it);

  // Wait for your turn.
  while(lock->owner != ticket){}
}

[[rc::manual_proof("refinedc.linux.pkvm.spinlock:spinlock_proof, "
                   "type_hyp_spin_unlock")]]
static inline void hyp_spin_unlock(hyp_spinlock_t *lock){
  // You are the current owner, so you can retrieve your ticket value.
  u16 ticket = lock->owner;

  // Check if your ticket was the last one.
  if(ticket == LAST_TICKET){
    // Give up the lock, and reset it to the first ticket.
    lock->owner = 0;

    // Also reset the ticket.
    lock->next = 0;
  } else {
    // Give up the lock, and give it to the owner of the next ticket.
    lock->owner = ticket + 1;
  }
}
