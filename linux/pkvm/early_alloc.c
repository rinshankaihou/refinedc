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
[[rc::refined_by("base : loc", "given : Z", "remaining : Z")]]
[[rc::let("z_cur : Z = {(base.2 + given * PAGE_SIZE)%Z}")]]
[[rc::let("z_end : Z = {(base.2 + (given + remaining) * PAGE_SIZE)%Z}")]]
[[rc::constraints("{0 ≤ given}", "{0 ≤ remaining}")]]
region {
  [[rc::field("z_end @ int<uintptr_t>")]] uintptr_t end;
  [[rc::field("z_cur @ int<uintptr_t>")]] uintptr_t cur;
  [[rc::field("own_constrained<nonshr_constraint<"
                 "{(base.1, z_cur) ◁ₗ uninit (PAGES (Z.to_nat remaining))}>, "
                 "base @ ptr<{Z.to_nat ((given + remaining) * PAGE_SIZE)}>>"
                                      )]] unsigned char* base;
};

static struct region mem;

#define base (mem.base)
#define end (mem.end)
#define cur (mem.cur)

[[rc::parameters("base : loc", "given : Z", "remaining : Z")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::returns("given @ int<size_t>")]]
[[rc::ensures("global mem : {(base, given, remaining)} @ region")]]
[[rc::tactics("rewrite Z.add_simpl_l /PAGE_SIZE. solve_goal.")]]
[[rc::tactics("rewrite /PAGE_SIZE Z.add_simpl_l Z.shiftr_div_pow2 //= Z.div_mul //=.")]]
size_t hyp_early_alloc_nr_pages(void){
  return (cur - (uintptr_t) base) >> PAGE_SHIFT;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<PAGE>>")]]
[[rc::ensures("own p : zeroed<PAGE>")]]
extern void clear_page(void *to);

[[rc::parameters("base : loc", "given : Z", "remaining : Z", "n : Z")]]
[[rc::args("n @ int<u32>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::requires("{0 < n ≤ remaining}", "{n ≪ PAGE_SHIFT ≤ max_int u32}")]]
[[rc::returns("&own<uninit<PAGES<{Z.to_nat n}>>>")]]
[[rc::ensures("global mem : {(base, given + n, remaining - n)%Z} @ region")]]
[[rc::tactics("all: unfold PAGE_SIZE, PAGE_SHIFT in *; try solve_goal.")]]
[[rc::tactics("assert (0 ≤ n ≪ 12); last by lia. by apply Z.shiftl_nonneg.")]]
[[rc::tactics("transitivity max_alloc_end; last done; etransitivity; last exact H10; "
              "rewrite Z.shiftl_mul_pow2 -?Z.add_assoc => //=; apply -> Z.add_le_mono_l; lia.")]]
[[rc::tactics("rewrite Z.shiftl_mul_pow2 in H18 => //. lia.")]]
[[rc::tactics("rewrite Z.shiftl_mul_pow2 //=. lia.")]]
void *hyp_early_alloc_contig(unsigned int nr_pages){
  uintptr_t ret = cur, p;
  unsigned int i;

  if (!nr_pages)
    return NULL;

  rc_unfold(base);
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

[[rc::parameters("base : loc", "given : Z", "remaining : Z")]]
[[rc::args("uninit<void*>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::requires("{0 ≠ remaining}")]]
[[rc::returns("&own<uninit<PAGE>>")]]
[[rc::ensures("global mem : {(base, given + 1, remaining - 1)} @ region")]]
void *hyp_early_alloc_page(void *arg){
  rc_unfold(base);
  return hyp_early_alloc_contig(1);
}

[[rc::parameters("l : loc", "n : Z", "s : Z")]]
[[rc::args("l @ &own<uninit<PAGES<{Z.to_nat n}>>>", "s @ int<u32>")]]
[[rc::requires("{s = (n * PAGE_SIZE)%Z}")]]
[[rc::requires("global mem : uninit<struct_region>")]]
[[rc::ensures("global mem : {(l, 0, n)} @ region")]]
[[rc::tactics("all: unfold PAGES, PAGE_SIZE in *; solve_goal.")]]
void hyp_early_alloc_init(unsigned char* virt, unsigned int size){
  base = virt;
  end = (uintptr_t) ((uintptr_t) virt + size);
  cur = (uintptr_t) virt;
}
