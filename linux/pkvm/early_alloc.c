// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google LLC
 * Author: Quentin Perret <qperret@google.com>
 */
//#include <asm/kvm_pgtable.h>
//
//#include <nvhe/early_alloc.h>
//#include <nvhe/memory.h>

#include <asm/page-def.h>
#include <stddef.h>
#include <refinedc.h>
//@rc::import instances from refinedc.linux.pkvm.early_alloc (for proofs only)

//struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;
//s64 __ro_after_init hyp_physvirt_offset;
//
//static unsigned long base;
//static unsigned long end;
//static unsigned long cur;

struct
[[rc::refined_by("base : loc", "given : Z", "remaining : Z")]]
[[rc::let("z_cur : Z = {(base.2 + given * PAGE_SIZE)%Z}")]]
[[rc::let("z_end : Z = {(base.2 + (given + remaining) * PAGE_SIZE)%Z}")]]
[[rc::constraints("{0 ≤ given}", "{0 ≤ remaining}", "[alloc_global base]")]]
[[rc::constraints("{base.2 + (given + remaining) * PAGE_SIZE ≤ max_int u64}")]]
region {
  [[rc::field("z_end @ int<u64>")]]
  unsigned long end;
  [[rc::field("z_cur @ int<u64>")]]
  unsigned long cur;
  [[rc::field("own_constrained<nonshr_constraint<"
                 "{(base.1, z_cur) ◁ₗ uninit (PAGES (Z.to_nat remaining))}>, "
                 "base @ intptr<u64>>")]]
  unsigned long base;
};

static struct region mem;

#define base (mem.base)
#define end (mem.end)
#define cur (mem.cur)

[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("&own<place<p>>", "{0} @ int<u8>", "n @ int<u64>")]]
[[rc::requires("own p : uninit<{ly_with_align (Z.to_nat n) (Z.to_nat PAGE_SIZE)}>")]]
[[rc::ensures("own p : zeroed<{ly_with_align (Z.to_nat n) (Z.to_nat PAGE_SIZE)}>")]]
extern void memset(void *to, unsigned char c, unsigned long size);

[[rc::parameters("base : loc", "given : Z", "remaining : Z")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::returns("given @ int<size_t>")]]
[[rc::ensures("global mem : {(base, given, remaining)} @ region")]]
[[rc::tactics("all: rewrite Z.add_simpl_l; try solve_goal.")]]
[[rc::tactics("all: rewrite Z.shiftr_div_pow2 //= Z.div_mul //=.")]]
unsigned long hyp_early_alloc_nr_used_pages(void)
{
  return (cur - base) >> PAGE_SHIFT;
}

[[rc::parameters("base : loc", "given : Z", "remaining : Z", "n : Z")]]
[[rc::args("n @ int<u32>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::requires("{0 < n ≤ remaining}", "{n ≪ PAGE_SHIFT ≤ max_int u32}")]]
[[rc::returns("&own<zeroed<PAGES<{Z.to_nat n}>>>")]]
[[rc::ensures("global mem : {(base, given + n, remaining - n)%Z} @ region")]]
[[rc::tactics("all: try rewrite -> Z.shiftl_mul_pow2 in *; try lia.")]]
[[rc::tactics("all: rewrite ?ly_offset_PAGES; try solve_goal.")]]
void *hyp_early_alloc_contig(unsigned int nr_pages)
{
  unsigned long size = (nr_pages << PAGE_SHIFT);
  void *ret = copy_alloc_id(cur, (void*) base);

  if (!nr_pages)
    return NULL;

  if (end - cur < size)
    return NULL;

  cur += size;
  memset(ret, 0, size);

  return ret;
}

[[rc::parameters("base : loc", "given : Z", "remaining : Z")]]
[[rc::args("uninit<void*>")]]
[[rc::requires("global mem : {(base, given, remaining)} @ region")]]
[[rc::requires("{0 < remaining}")]]
[[rc::returns("&own<zeroed<PAGE>>")]]
[[rc::ensures("global mem : {(base, given + 1, remaining - 1)} @ region")]]
void *hyp_early_alloc_page(void *arg)
{
  return hyp_early_alloc_contig(1);
}

[[rc::parameters("l : loc", "n : Z", "s : Z")]]
[[rc::args("l @ &own<uninit<PAGES<{Z.to_nat n}>>>", "s @ int<u64>")]]
[[rc::requires("{s = (n * PAGE_SIZE)%Z}", "[alloc_global l]")]]
[[rc::requires("global mem : uninit<struct_region>")]]
[[rc::ensures("global mem : {(l, 0, n)} @ region")]]
[[rc::tactics("all: rewrite -> ly_size_PAGES in *; solve_goal.")]]
void hyp_early_alloc_init(void *virt, unsigned long size)
{
  //base = cur = (unsigned long)virt;
  base = (unsigned long)virt;
  cur = base;
  end = base + size;

  //hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
  //hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
  //hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;
}
