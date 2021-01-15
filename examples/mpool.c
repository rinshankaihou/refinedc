/*
 * Copyright 2018 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <refinedc.h>
#include <spinlock.h>

[[rc::parameters("p : loc", "size : loc", "align : nat")]]
[[rc::args("p @ ptr", "align @ int<size_t>", "size @ &own<uninit<size_t>>")]]
[[rc::exists("diff : nat")]]
[[rc::returns("{p +ₗ diff} @ ptr")]]
[[rc::ensures("own size : diff @ int<size_t>", "{(p +ₗ diff) `aligned_to` align}", "{diff < align}")]]
unsigned char * round_pointer_up(unsigned char *p, size_t align, size_t *size);


typedef struct [[rc::parameters("entry_size: nat")]]
               [[rc::refined_by("len: nat")]]
               [[rc::ptr_type("mpool_chunk_t : {(0 < len)%nat} @ optional<&own<...>>")]]
               [[rc::exists("local: nat", "next: nat", "ly : layout")]]
               [[rc::size("ly")]]
               [[rc::constraints("{(len = local + next)%nat}", "{local > 0}",
                                 "{ly = ly_with_align (local * entry_size) entry_size}")]]
mpool_chunk {

  [[rc::field("{local * entry_size} @ int<size_t>")]]
  size_t size;

  [[rc::field("next @ mpool_chunk_t<entry_size>")]]
  struct mpool_chunk *next_chunk;
}* mpool_chunk_t;

typedef struct [[rc::parameters("entry_size: nat")]]
               [[rc::refined_by("len: nat")]]
               [[rc::ptr_type("mpool_entry_t : {(0 < len)%nat} @ optional<&own<...>>")]]
               [[rc::size("{ly_with_align entry_size entry_size}")]]
mpool_entry {

  [[rc::field("{(len - 1)%nat} @ mpool_entry_t<entry_size>")]]
  struct mpool_entry *next;
}* mpool_entry_t;

/* #include "hf/mpool.h" */
struct [[rc::parameters("entry_size: nat")]]
       [[rc::refined_by("entries: nat")]]
       [[rc::exists("lid: lock_id")]]
       [[rc::constraints("{is_power_of_two entry_size}",
                         "{layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size}",
                         "{layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size}")]]
mpool {

  [[rc::field("entry_size @ int<size_t>")]]
  size_t entry_size;

  [[rc::field("spinlock<lid>")]]
  struct spinlock lock;

  [[rc::field("spinlocked_ex<lid, {\"locked\"}, entries, λ entries. ...>")]]
  struct [[rc::exists("entries_in_chunks: nat", "entries_in_entry_list: nat")]]
         [[rc::constraints("{(entries = entries_in_chunks + entries_in_entry_list)%nat}")]]
    mpool_locked_inner {
    // Here it is important that entries is only propagated with we have an owned reference to
    // the mpool, but not for a shared reference. This is because when we have a shared reference
    // we cannot know how many entries are in the mpool, because it might be modified concurrently.

    [[rc::field("entries_in_chunks @ mpool_chunk_t<entry_size>")]]
    mpool_chunk_t chunk_list;
    [[rc::field("entries_in_entry_list @ mpool_entry_t<entry_size>")]]
    mpool_entry_t entry_list;
  } locked;

  // TODO: This should be "optional<&shr<mpool<entry_size>>>"
  [[rc::field("optional<&shr<∃ n. n @ mpool<entry_size>>>")]]
  struct mpool *fallback;
};


bool mpool_add_chunk(struct mpool *p, void *begin, size_t size);
void mpool_free(struct mpool *p, void *ptr);

/**
 * Initialises the given memory pool with the given entry size, which must be
 * at least the size of two pointers.
 *
 * All entries stored in the memory pool will be aligned to at least the entry
 * size.
 */
[[rc::parameters("p : loc", "entry_size : nat")]]
[[rc::args("p @ &own<uninit<struct_mpool>>", "entry_size @ int<size_t>")]]
[[rc::requires("{layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size}",
               "{layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size}",
               "{is_power_of_two entry_size}")]]
[[rc::ensures("own p : {0%nat} @ mpool<entry_size>")]]
void mpool_init(struct mpool *p, size_t entry_size)
{
  p->entry_size = entry_size;
  p->locked.chunk_list = NULL;
  p->locked.entry_list = NULL;
  p->fallback = NULL;
  sl_init(&p->lock);
}

/**
 * Initialises the given memory pool by replicating the properties of `from`. It
 * also pulls the chunk and free lists from `from`, consuming all its resources
 * and making them available via the new memory pool.
 */
[[rc::parameters("p : loc", "entry_size : nat", "q : own_state", "entries : nat", "from : loc")]]
[[rc::args("p @ &own<uninit<struct_mpool>>", "from @ &frac<q, entries @ mpool<entry_size>>")]]
[[rc::exists("rentries : nat")]]
[[rc::ensures("own p : rentries @ mpool<entry_size>", "frac q from : {0%nat} @ mpool<entry_size>",
              "{q = Own → rentries = entries}")]]
void mpool_init_from(struct mpool *p, struct mpool *from)
{
  mpool_init(p, from->entry_size);

  sl_lock(&from->lock);
  rc_unlock(from->locked);

  p->locked.chunk_list = from->locked.chunk_list;
  p->locked.entry_list = from->locked.entry_list;
  p->fallback = from->fallback;

  from->locked.chunk_list = NULL;
  from->locked.entry_list = NULL;
  /* TODO: We can only reset the fallback if it is part of the lock */
  /* from->locked.fallback = NULL; */
  sl_unlock(&from->lock);
}

/**
 * Initialises the given memory pool with a fallback memory pool if this pool
 * runs out of memory.
 */
[[rc::parameters("p : loc", "entry_size : nat", "q : own_state", "entries : nat", "fallback : loc")]]
[[rc::args("p @ &own<uninit<struct_mpool>>", "fallback @ &shr<entries @ mpool<entry_size>>")]]
[[rc::ensures("own p : {0%nat} @ mpool<entry_size>")]]
void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback)
{
  mpool_init(p, fallback->entry_size);
  p->fallback = fallback;
}

/**
 * Finishes the given memory pool, giving all free memory to the fallback pool
 * if there is one.
 */
[[rc::parameters("p : loc", "n : nat", "entry_size : nat")]]
[[rc::args("p @ &own<n @ mpool<entry_size>>")]]
[[rc::ensures("own p : uninit<struct_mpool>")]]
void mpool_fini(struct mpool *p) {
  struct mpool_entry *entry;
  struct mpool_chunk *chunk;

  if (p->fallback == NULL) {
    return;
  }

  entry = p->locked.entry_list;
  chunk = p->locked.chunk_list;
  /* Merge the freelist into the fallback. */
  [[rc::inv_vars("entry : mpool_entry_t<entry_size>")]]
  [[rc::inv_vars("chunk : mpool_chunk_t<entry_size>")]]
  [[rc::inv_vars("p : p @ &own<struct<struct_mpool, entry_size @ int<size_t>, uninit<struct_spinlock>, uninit<struct_mpool_locked_inner>, &shr<∃ n. n @ mpool<entry_size>>>>")]]
  while (entry != NULL) {
    void *ptr1 = entry;
    entry = entry->next;
    mpool_free(p->fallback, ptr1);
  }

  /* Merge the chunk list into the fallback. */
  [[rc::inv_vars("entry : mpool_entry_t<entry_size>")]]
  [[rc::inv_vars("chunk : mpool_chunk_t<entry_size>")]]
  [[rc::inv_vars("p : p @ &own<struct<struct_mpool, entry_size @ int<size_t>, uninit<struct_spinlock>, uninit<struct_mpool_locked_inner>, &shr<∃ n. n @ mpool<entry_size>>>>")]]
  while (chunk != NULL) {
    void *ptr2 = chunk;
    size_t size = chunk->size;

    chunk = chunk->next_chunk;
    mpool_add_chunk(p->fallback, ptr2, size);
  }

  p->locked.chunk_list = NULL;
  p->locked.entry_list = NULL;
  p->fallback = NULL;
}


/**
 * Adds a contiguous chunk of memory to the given memory pool. The chunk will
 * eventually be broken up into entries of the size held by the memory pool.
 *
 * Only the portions aligned to the entry size will be added to the pool.
 *
 * Returns true if at least a portion of the chunk was added to pool, or false
 * if none of the buffer was usable in the pool.
 */
[[rc::parameters("p : loc", "q : own_state", "n : nat", "entry_size : nat", "m : nat")]]
[[rc::args("p @ &frac<q, n @ mpool<entry_size>>",
           "&own<uninit<{ly_with_align (m * entry_size) entry_size}>>",
           "{m * entry_size} @ int<size_t>")]]
[[rc::returns("{Z_of_bool (bool_decide (0 < m)%nat)} @ int<bool_it>")]]
[[rc::ensures("frac q p : {(n + m)%nat} @ mpool<entry_size>")]]
  [[rc::tactics("all: try by destruct m => //=; solve_goal.")]]
bool mpool_add_chunk(struct mpool *p, void *begin, size_t size)
{
  struct mpool_chunk *chunk;

  rc_unfold(p->entry_size);

  // no rounding necessary since begin is guaranteed to be aligned
  if (size == (size_t) 0) {
    return false;
  }

  chunk = begin;
  chunk->size = size;

  sl_lock(&p->lock);
  rc_unlock(p->locked);
  chunk->next_chunk = p->locked.chunk_list;
  p->locked.chunk_list = chunk;
  sl_unlock(&p->lock);

  return true;
}

/**
 * Allocates an entry from the given memory pool, if one is available. The
 * fallback will not be used even if there is one.
 */
[[rc::parameters("p : loc", "q : own_state", "n : nat", "entry_size : nat")]]
[[rc::args("p @ &frac<q, n @ mpool<entry_size>>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ optional<&own<uninit<{ly_with_align entry_size entry_size}>>>")]]
[[rc::ensures("frac q p : {(n-1)%nat} @ mpool<entry_size>", "{q = Own → b ↔ (0 < n)%nat}")]]
  [[rc::tactics("all: try by destruct x1 as [|[]]; try solve_goal; zify; ring_simplify; solve_goal.")]]
static void *mpool_alloc_no_fallback(struct mpool *p)
{
  void *ret;
  struct mpool_chunk *chunk;
  struct mpool_chunk *new_chunk;

  /* Fetch an entry from the free list if one is available. */
  sl_lock(&p->lock);
  rc_unlock(p->locked);
  if (p->locked.entry_list != NULL) {
    struct mpool_entry *entry = p->locked.entry_list;

    p->locked.entry_list = entry->next;
    ret = entry;
    goto exit;
  }

  /* There was no free list available. Try a chunk instead. */
  chunk = p->locked.chunk_list;
  if (chunk == NULL) {
    /* The chunk list is also empty, we're out of entries. */
    ret = NULL;
    goto exit;
  }

  if (p->entry_size >= chunk->size) {
    p->locked.chunk_list = chunk->next_chunk;
  } else {
    new_chunk = (struct mpool_chunk *)((unsigned char *)chunk + p->entry_size);
    new_chunk->next_chunk = chunk->next_chunk;
    new_chunk->size = chunk->size - p->entry_size;
    p->locked.chunk_list = new_chunk;
  }

  ret = chunk;

exit:
  sl_unlock(&p->lock);

  return ret;
}

/**
 * Allocates an entry from the given memory pool, if one is available. If there
 * isn't one available, try and allocate from the fallback if there is one.
 */
[[rc::parameters("p : loc", "q : own_state", "n : nat", "entry_size : nat")]]
[[rc::args("p @ &frac<q, n @ mpool<entry_size>>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ optional<&own<uninit<{ly_with_align entry_size entry_size}>>>")]]
[[rc::ensures("frac q p : {(n-1)%nat} @ mpool<entry_size>", "{q = Own → (0 < n)%nat → b}")]]
void *mpool_alloc(struct mpool *p) {
  void *ret = mpool_alloc_no_fallback(p);
  if (ret != NULL) {
    return ret;
  }
  p = p->fallback;

  [[rc::inv_vars("p : optional<&shr<mpool<entry_size>>>")]]
  [[rc::constraints("frac q p : {(n - 1)%nat} @ mpool<entry_size>", "{q = Own → n = 0%nat}")]]
  while (p != NULL) {
    ret = mpool_alloc_no_fallback(p);
    if (ret != NULL) {
      return ret;
    }
    p = p->fallback;
  }

  return NULL;
}

/**
 * Frees an entry back into the memory pool, making it available for reuse.
 *
 * This is meant to be used for freeing single entries. To free multiple
 * entries, one must call mpool_add_chunk instead.
 */
[[rc::parameters("p : loc", "q : own_state", "n : nat", "entry_size : nat", "ptr : loc")]]
[[rc::args("p @ &frac<q, n @ mpool<entry_size>>", "ptr @ &own<uninit<{ly_with_align entry_size entry_size}>>")]]
[[rc::ensures("frac q p : {(n + 1)%nat} @ mpool<entry_size>")]]
void mpool_free(struct mpool *p, void *ptr) {
  struct mpool_entry *e = ptr;

  /* Store the newly freed entry in the front of the free list. */
  sl_lock(&p->lock);
  rc_unlock(p->locked);
  e->next = p->locked.entry_list;
  p->locked.entry_list = e;
  sl_unlock(&p->lock);
}

/**
 * Allocates a number of contiguous and aligned entries. If a suitable
 * allocation could not be found, the fallback will not be used even if there is
 * one.
 */
[[rc::parameters("p : loc", "q : own_state", "n : nat", "entry_size : nat", "count : nat", "align : nat")]]
[[rc::args("p @ &frac<q, n @ mpool<entry_size>>", "count @ int<size_t>", "align @ int<size_t>")]]
[[rc::requires("{(align * entry_size + count * entry_size)%Z ∈ size_t}", "{is_power_of_two align}")]]
[[rc::exists("n2 : nat")]]
[[rc::returns("optional<&own<uninit<{ly_with_align (count * entry_size) (align * entry_size)}>>>")]]
[[rc::ensures("frac q p : n2 @ mpool<entry_size>", "{q = Own → n2 <= n}")]]
  [[rc::tactics("all: try by destruct o'; solve_goal.")]]
  [[rc::tactics("all: try by apply mult_le_compat_r; solve_goal.")]]
  [[rc::tactics("all: try by repeat progress rewrite /ly_size/=; have : (x4 - Z.to_nat o' - count > 0)%nat; solve_goal.")]]
void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count, size_t align)
{
  struct mpool_chunk **prev;
  void *ret = NULL;

  align *= p->entry_size;

  sl_lock(&p->lock);
  rc_unlock(p->locked);

  /*
   * Go through the chunk list in search of one with enough room for the
   * requested allocation
   */
  prev = &p->locked.chunk_list;

  [[rc::block]]
  [[rc::exists("pc : loc",
               "entries_in_chunks1 : nat", "entries_in_chunks2 : nat",
               "entries_in_entry_list : nat")]]
  [[rc::inv_vars("align : {align * entry_size} @ int<size_t>", "ret : null", "p : ∃ l. place<l>",
                 "prev : pc @ &own<entries_in_chunks2 @ mpool_chunk_t<entry_size>>")]]
  [[rc::constraints("[p at{struct_mpool}ₗ \"locked\" ◁ₗ struct struct_mpool_locked_inner [wand_ex (λ x, pc ◁ₗ x @ mpool_chunk_t entry_size) (λ x, (entries_in_chunks1 + x)%nat @ mpool_chunk_t entry_size) ; entries_in_entry_list @ mpool_entry_t entry_size]]",
                    "{shelve_hint (q = Own → n = (entries_in_chunks1 + entries_in_chunks2 + entries_in_entry_list)%nat)}")]]
  while (*prev != NULL) {
    unsigned char* start;
    struct mpool_chunk *new_chunk;
    struct mpool_chunk *chunk = *prev;
    size_t before_start;

    /* Round start address up to the required alignment. */
    round_pointer_up((unsigned char *)chunk, align, &before_start);

    /*
     * Calculate where the new chunk would be if we consume the
     * requested number of entries. Then check if this chunk is big
     * enough to satisfy the request.
     */
    if (before_start + count * p->entry_size <= chunk->size) {
      size_t chunk_size = chunk->size;
      struct mpool_chunk *chunk_next = chunk->next_chunk;
      rc_to_uninit(*chunk);
      start = (unsigned char *)chunk + before_start;
      /* Remove the consumed area. */
      if (before_start + count * p->entry_size == chunk_size) {
        *prev = chunk_next;
      } else {
        new_chunk = (struct mpool_chunk *)(start + (count * p->entry_size));
        new_chunk->size = chunk_size - (before_start + count * p->entry_size);
        new_chunk->next_chunk = chunk_next;
        *prev = new_chunk;
      }

      /*
       * Add back the space consumed by the alignment
       * requirement, if it's big enough to fit an entry.
       */
      if (before_start >= p->entry_size) {
        chunk->next_chunk = *prev;
        *prev = chunk;
        chunk->size = before_start;
      }

      rc_uninit_strengthen_align(*start);
      ret = (void *)start;
      break;
    }

    prev = &chunk->next_chunk;
  }

  sl_unlock(&p->lock);

  return ret;
}

/**
 * Allocates a number of contiguous and aligned entries. This is a best-effort
 * operation and only succeeds if such entries can be found in the chunks list
 * or the chunks of the fallbacks (i.e., the entry list is never used to satisfy
 * these allocations).
 *
 * The alignment is specified as the number of entries, that is, if `align` is
 * 4, the alignment in bytes will be 4 * entry_size.
 *
 * The caller can enventually free the returned entries by calling
 * mpool_add_chunk.
 */
[[rc::parameters("p : loc", "q : own_state", "n : nat", "entry_size : nat", "count : nat", "align : nat")]]
[[rc::args("p @ &frac<q, n @ mpool<entry_size>>", "count @ int<size_t>", "align @ int<size_t>")]]
[[rc::requires("{(align * entry_size + count * entry_size)%Z ∈ size_t}", "{is_power_of_two align}")]]
[[rc::exists("n2 : nat")]]
[[rc::returns("optional<&own<uninit<{ly_with_align (count * entry_size) (align * entry_size)}>>>")]]
[[rc::ensures("frac q p : n2 @ mpool<entry_size>", "{q = Own → n2 <= n}")]]
void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align)
{
  void *ret = mpool_alloc_contiguous_no_fallback(p, count, align);

  if (ret != NULL) {
    return ret;
  }

  p = p->fallback;
  [[rc::exists("n2 : nat")]]
  [[rc::inv_vars("p : optional<&shr<mpool<entry_size>>>")]]
  [[rc::constraints("frac q p : n2 @ mpool<entry_size>", "{q = Own → n2 <= n}")]]
  while (p != NULL) {
    ret = mpool_alloc_contiguous_no_fallback(p, count, align);

    if (ret != NULL) {
      return ret;
    }

    p = p->fallback;

  }

  return NULL;
}
