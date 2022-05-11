#pragma once

#include <assert.h>
#include <stdint.h>
#include <stddef.h>

#if defined (__refinedc__)
#include "refinedc_builtins_specs.h"
#endif

/* let's support 256 priorities, with 0 being the highest priority */
typedef uint8_t priority_t;
#define NUM_PRIORITIES (UINT8_MAX + 1)

/* a bitmap of "non-empty queue" indicators */
typedef struct {
  uint64_t bits[4];
} prio_bitmap_t;

typedef int priority_search_t;

static inline
void prio_level_init(prio_bitmap_t *bm)
{
  for(int lvl = 0; lvl < 4; lvl += 1) {
    bm->bits[lvl] = 0;
  }
}

/* find the maximum priority level with pending work, or return -1 */
static inline
priority_search_t highest_pending_priority(prio_bitmap_t *bm) {
  int offset = -1;
  for (int i = 0; i < 4; i++) {
    int first_bit = __builtin_ffsll(bm->bits[i]);
    if (first_bit) {
      return first_bit + offset;
    } else {
      offset += 64;
    }
  }
  return -1;
}

/* predicate: did we find a non-empty priority level? */
static inline
int priority_search_none_found(priority_search_t result) {
  return result < 0;
}

/* set the bit corresponding to the given priority */
static inline
void priority_level_set(prio_bitmap_t *bm, priority_t prio) {
  uint8_t word = prio / 64;
  uint8_t bit  = prio % 64;
  bm->bits[word] |= (((uint64_t) 1) << bit);
}

/* clear the bit corresponding to the given priority */
static inline
void priority_level_clear(prio_bitmap_t *bm, priority_t prio) {
  uint8_t word = prio / 64;
  uint8_t bit  = prio % 64;
  bm->bits[word] &= ~(((uint64_t) 1) << bit);
}
