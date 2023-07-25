// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google LLC
 * Author: Quentin Perret <qperret@google.com>
 */

// #include <asm/kvm_hyp.h>
// #include <nvhe/gfp.h>

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>
#include <refinedc.h>

//@rc::import page_alloc_def from refinedc.linux.casestudies.page_alloc_find_buddy


typedef unsigned long long u64;
typedef signed long long s64;
typedef u64 phys_addr_t;
typedef u64 gfp_t;

#define PAGE_SIZE 4096
#define PAGE_SHIFT 12

/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* #include <asm/page.h> */

/* #include <linux/types.h> */

#define HYP_MEMBLOCK_REGIONS 128
struct [[rc::refined_by("refcount : Z", "order : Z")]]
hyp_page {
	[[rc::field("refcount @ int<u16>")]]
	unsigned short refcount;
	[[rc::field("order @ int<u16>")]]
	unsigned short order;
};

extern s64 hyp_physvirt_offset;
// TODO: frontend seems to get confused by having both [extern u64 x]
// and [u64 x] in the same file: rc::global does not seem to work anymore
// extern u64 __hyp_vmemmap;
[[rc::parameters("vmemmap : loc")]]
[[rc::global("vmemmap @ intptr<u64>")]]
u64 __hyp_vmemmap;
#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)
/* #define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap) */

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(phys)	((void *)((phys_addr_t)(phys) - hyp_physvirt_offset))

static inline void *hyp_phys_to_virt(phys_addr_t phys)
{
	return __hyp_va(phys);
}

static inline phys_addr_t hyp_virt_to_phys(void *addr)
{
	return __hyp_pa(addr);
}

#define hyp_phys_to_pfn(phys)	((phys) >> PAGE_SHIFT)
#define hyp_pfn_to_phys(pfn)	((phys_addr_t)((pfn) << PAGE_SHIFT))
/* #define hyp_phys_to_page(phys)	(&hyp_vmemmap[hyp_phys_to_pfn(phys)]) */
#define hyp_phys_to_page(phys)	(hyp_vmemmap + hyp_phys_to_pfn(phys))
#define hyp_virt_to_page(virt)	hyp_phys_to_page(__hyp_pa(virt))
#define hyp_virt_to_pfn(virt)	hyp_phys_to_pfn(__hyp_pa(virt))

#define hyp_page_to_pfn(page)	((struct hyp_page *)(page) - hyp_vmemmap)
#define hyp_page_to_phys(page)  hyp_pfn_to_phys((hyp_page_to_pfn(page)))
#define hyp_page_to_virt(page)	__hyp_va(hyp_page_to_phys(page))
#define hyp_page_to_pool(page)	(((struct hyp_page *)page)->pool)

#endif /* __KVM_HYP_MEMORY_H */

/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef __KVM_HYP_GFP_H
#define __KVM_HYP_GFP_H

/* #include <linux/list.h> */

/* #include <nvhe/memory.h> */
/* #include <nvhe/spinlock.h> */

#define HYP_MAX_ORDER	11U
//@rc::inlined Definition HYP_MAX_ORDER : nat := Z.to_nat 11.
#define HYP_NO_ORDER	UINT_MAX
//@rc::inlined Definition HYP_NO_ORDER : Z := max_int u32.

struct [[rc::refined_by("pages : {list (Z * Z)}",
						"npages : nat",
						"vmemmap : loc",
						"range_start_idx : Z",
						"max_order : Z")]]
	   [[rc::exists("range_start : Z", "range_end : Z")]]
       [[rc::constraints("[initialized \"__hyp_vmemmap\" vmemmap]")]]
       [[rc::constraints("{(length pages =@{Z} range_start_idx + npages)%Z}")]]
       [[rc::constraints("{(range_start = range_start_idx ≪ PAGE_SHIFT)%Z}")]]
       [[rc::constraints("{(range_end = range_start + npages ≪ PAGE_SHIFT)%Z}")]]
       [[rc::constraints("{(0 <= range_start_idx)%Z}")]]
 hyp_pool {
	/* hyp_spinlock_t lock; */
	/* struct list_head free_area[HYP_MAX_ORDER + 1]; */
	[[rc::field("own_constrained<nonshr_constraint<{vmemmap ◁ₗ !{ array<struct_hyp_page, {pages `at_type` hyp_page}> } }>, range_start @ int<u64>>")]]
	phys_addr_t range_start;
	[[rc::field("range_end @ int<u64>")]]
	phys_addr_t range_end;
	[[rc::field("max_order @ int<u16>")]]
	unsigned short max_order;
};

/* GFP flags */
#define HYP_GFP_NONE	0
#define HYP_GFP_ZERO	1

/* Allocation */
void *hyp_alloc_pages(struct hyp_pool *pool, gfp_t mask, unsigned int order);
void hyp_get_page(void *addr);
void hyp_put_page(void *addr);

/* Used pages cannot be freed */
int hyp_pool_init(struct hyp_pool *pool, phys_addr_t phys,
		  unsigned int nr_pages, unsigned int used_pages);
#endif /* __KVM_HYP_GFP_H */

//u64 __hyp_vmemmap;
/* [[rc::parameters("vmemmap : loc")]] */
/* [[rc::global("&own<place<vmemmap>>")]] */
/* void *__hyp_vmemmap; */

/*
 * Example buddy-tree for a 4-pages physically contiguous pool:
 *
 *                 o : Page 3
 *                /
 *               o-o : Page 2
 *              /
 *             /   o : Page 1
 *            /   /
 *           o---o-o : Page 0
 *    Order  2   1 0
 *
 * Example of requests on this zon:
 *   __find_buddy(pool, page 0, order 0) => page 1
 *   __find_buddy(pool, page 0, order 1) => page 2
 *   __find_buddy(pool, page 1, order 0) => page 0
 *   __find_buddy(pool, page 2, order 0) => page 3
 */
[[rc::parameters("pool : loc", "pageloc : loc", "page : Z", "vmemmap : loc", "pages : {list (Z * Z)}", "npages : nat", "range_start_idx : Z", "order : Z", "max_order : Z")]]
[[rc::args("pool @ &own<{(pages, npages, vmemmap, range_start_idx, max_order)} @ hyp_pool>",
		   "pageloc @ &own<array_ptr<struct_hyp_page, vmemmap, page, {length pages}>>", "order @ int<u32>")]]
[[rc::requires("{0 <= page ≪ 12 <= max_int ptrdiff_t}", "{0 < length pages}", "{0 <= order <= HYP_MAX_ORDER}")]]
[[rc::returns("{range_start_idx <= find_buddy vmemmap order page < range_start_idx + npages} @ optional<&own<array_ptr<struct_hyp_page, vmemmap, {find_buddy vmemmap order page}, {length pages}>>, null>")]]
[[rc::ensures("own pool : {(pages, npages, vmemmap, range_start_idx, max_order)} @ hyp_pool")]]
[[rc::ensures("own pageloc : array_ptr<struct_hyp_page, vmemmap, page, {length pages}>")]]
[[rc::tactics("all: unfold find_buddy, PAGE_SHIFT, PAGE_SIZE in *.")]]
[[rc::tactics("all: repeat match goal with | H : _ = Lt |- _ => rewrite -/(Z.lt _ _) in H end.")]]
[[rc::tactics("all: try by etrans; [|done]; rewrite Z.shiftl_mul_pow2 //; lia.")]]
[[rc::tactics("all: try by rewrite Z.shiftl_mul_pow2 //; etrans; [ apply: Z.mul_le_mono_nonneg_l; [done| ]; apply: (Z.pow_le_mono_r _ _ 11) |].")]]
[[rc::tactics("all: try by move =>/find_buddy_result_eq; solve_goal.")]]
[[rc::tactics("all: try by eapply (find_buddy_result' page range_start_idx order npages); solve_goal.")]]
[[rc::tactics("all: try by eapply find_buddy_result_eq; solve_goal.")]]
static struct hyp_page *__find_buddy(struct hyp_pool *pool, struct hyp_page *p,
				     unsigned int order)
{
	rc_unfold(pool->range_start);
	phys_addr_t addr = hyp_page_to_phys(p);

	addr ^= (PAGE_SIZE << order);
	if (addr < pool->range_start || addr >= pool->range_end)
		return NULL;

	return hyp_phys_to_page(addr);
}
