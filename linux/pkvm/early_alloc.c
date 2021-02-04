// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google LLC
 * Author: Quentin Perret <qperret@google.com>
 */

#include <asm/page-def.h>
#include <stddef.h>
#include <stdint.h>
#include <refinedc.h>

//@rc::import instances from refinedc.linux.pkvm.early_alloc (for proofs only)

struct
[[rc::refined_by("base : loc", "given : nat", "remaining : nat")]]
[[rc::let("z_cur : Z = {(base.2 + given * PAGE_SIZE)%Z}")]]
[[rc::let("z_end : Z = {(base.2 + (given + remaining) * PAGE_SIZE)%Z}")]]
region {
  [[rc::field("own_constrained<nonshr_constraint<"
                 "{(base.1, z_cur) ◁ₗ uninit (PAGES remaining)}>, "
                 "value<void*, base>>")]] unsigned char* base;
  [[rc::field("z_end @ int<uintptr_t>")]] uintptr_t end;
  [[rc::field("z_cur @ int<uintptr_t>")]] uintptr_t cur;
};

static struct region mem;

#define base (mem.base)
#define end (mem.end)
#define cur (mem.cur)

[[rc::parameters("base : loc", "given : nat", "remaining : nat")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::returns("given @ int<size_t>")]]
[[rc::ensures("global mem : {(base, given, remaining)} @ region")]]
[[rc::trust_me]] // FIXME
size_t hyp_early_alloc_nr_pages(void){
  return (cur - (uintptr_t) base) >> PAGE_SHIFT;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<PAGE>>")]]
[[rc::ensures("own p : zeroed<PAGE>")]]
extern void clear_page(void *to);

[[rc::parameters("base : loc", "given : nat", "remaining : nat", "n : nat")]]
[[rc::args("n @ int<u32>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region", "{0%nat < n ≤ remaining}")]]
[[rc::returns("&own<uninit<PAGES<n>>>")]]
[[rc::ensures("global mem : {(base, given + n, remaining - n)%nat} @ region")]]
[[rc::trust_me]] // FIXME
void *hyp_early_alloc_contig(unsigned int nr_pages){
  uintptr_t ret = cur, p;
  unsigned int i;

  if (!nr_pages)
    return NULL;

  cur += nr_pages << PAGE_SHIFT;
  if (cur > end) {
    cur = ret;
    return NULL;
  }

  // FIXME change spec with zeroed.
  //for (i = 0; i < nr_pages; i++) {
  //  p = ret + (i << PAGE_SHIFT);
  //  clear_page((void *)(p));
  //}

  return rc_copy_alloc_id((void *) ret, base);
}

[[rc::parameters("base : loc", "given : nat", "remaining : nat")]]
[[rc::args("uninit<void*>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region", "{remaining ≠ 0%nat}")]]
[[rc::returns("&own<uninit<PAGE>>")]]
[[rc::ensures("global mem : {(base, given + 1, remaining - 1)%nat} @ region")]]
void *hyp_early_alloc_page(void *arg){
  return hyp_early_alloc_contig(1);
}

[[rc::parameters("l : loc", "n : nat", "s : Z")]]
[[rc::args("l @ &own<uninit<PAGES<n>>>", "s @ int<u32>")]]
[[rc::requires("{s = (n * PAGE_SIZE)%Z}")]]
[[rc::requires("global mem : uninit<struct_region>")]]
[[rc::ensures("global mem : {(l, 0%nat, n)} @ region")]]
void hyp_early_alloc_init(unsigned char* virt, unsigned int size){
  base = virt;
  end = (uintptr_t) ((uintptr_t) virt + size);
  cur = (uintptr_t) virt;
}
