#pragma once

#include <assert.h>
#include <stdint.h>
#include <stddef.h>

#if defined (__refinedc__)
#include "refinedc_builtins_specs.h"
#endif

//@rc::import priority_modified_extra from refinedc.examples.scheduler.src.fdsched

/* let's support 64 priorities, with 0 being the highest priority */
 typedef uint8_t priority_t;
// #define NUM_PRIORITIES (UINT8_MAX + 1)
#define NUM_PRIORITIES 64

typedef struct
[[rc::refined_by("bitmap : Z")]]
[[rc::ptr_type("prio_bitmap_t : ... ")]]
{
  [[rc::field("bitmap @ int<u64>")]]
  uint64_t bits;
} prio_bitmap_t;

typedef int priority_search_t;

[[rc::parameters("p : loc","bm : Z")]]
[[rc::args("p @ &own<bm  @ prio_bitmap_t>")]]
[[rc::ensures("own p : {0} @ prio_bitmap_t")]]
static inline
void prio_level_init(prio_bitmap_t *bm)
{
  bm->bits = 0;
}


/* find the maximum priority level with pending work, or return -1 */
[[rc::parameters("p : loc","bm : Z")]]
[[rc::args("p @ &own<bm  @ prio_bitmap_t>")]]
[[rc::returns("{Z_least_significant_one bm} @int<i32>")]]
[[rc::ensures("own p : prio_bitmap_t")]]
[[rc::tactics("all: try by have := Z_least_significant_one_lower_bound bm; solve_goal.")]]
static inline
priority_search_t highest_pending_priority(prio_bitmap_t *bm) {
  int offset = -1;
  int first_bit = __builtin_ffsll(bm->bits);
  if (first_bit != 0)
    return first_bit -1;
  else
    return -1;
}

/* predicate: did we find a non-empty priority level? */
[[rc::parameters("res : Z")]]
[[rc::args("res @ int<i32>")]]
[[rc::returns("{bool_decide (res < 0)} @ boolean<i32>")]]
static inline
int priority_search_none_found(priority_search_t result) {
  return result < 0;
}

/* set the bit corresponding to the given priority */
[[rc::parameters("p : loc","priority : Z","bm : Z")]]
[[rc::args("p @ &own<bm  @ prio_bitmap_t>","priority @ int<u8>")]]
[[rc::requires("{priority < 64}", "{0 <= priority}")]]
[[rc::ensures("own p : {Z.setbit bm priority} @ prio_bitmap_t")]]
[[rc::tactics("by apply Z_shiftl_1_range.")]]
static inline
void priority_level_set(prio_bitmap_t *bm, priority_t prio) {
  bm->bits |= (((uint64_t) 1) << prio);
}

/* clear the bit corresponding to the given priority */
[[rc::parameters("p : loc","priority : Z","bm : Z")]]
[[rc::args("p @ &own<bm  @ prio_bitmap_t>","priority @ int<u8>")]]
[[rc::requires("{priority < 64}", "{0 <= priority}")]]
[[rc::ensures("own p : {Z.clearbit bm priority} @ prio_bitmap_t")]]
[[rc::lemmas("clearbit_equiv")]]
[[rc::tactics("by apply Z_shiftl_1_range.")]]
void priority_level_clear(prio_bitmap_t *bm, priority_t prio) {
  bm->bits &= ~(((uint64_t) 1) << prio);
}
