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
#include "../examples/include/spinlock.h"
#include <refinedc.h>

#define hyp_spinlock_t struct spinlock
#define hyp_spin_lock sl_lock
#define hyp_spin_unlock sl_unlock
#define hyp_spin_lock_init sl_init

//@rc::require refinedc.linux.casestudies.page_alloc
//@rc::import page_alloc_def from refinedc.linux.casestudies.page_alloc


[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<PAGE_LAYOUT<{1}>>>")]]
[[rc::ensures("own p : zeroed<PAGE_LAYOUT<{1}>>")]]
extern void clear_page(void *to);

void *memset(void* ptr, int value, size_t num);

void hyp_panic() {
	assert(0);
}


typedef unsigned long long u64;
typedef signed long long s64;
typedef u64 phys_addr_t;
typedef u64 gfp_t;

#define PAGE_SIZE 4096
#define PAGE_SHIFT 12
#define EINVAL 22

#define WRITE_ONCE(a, b) ((a) = (b))
#define READ_ONCE(a) (a)

#define container_of(ptr, type, member) (type *)( (char *)(ptr) - offsetof(type,member) )

/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _LINUX_LIST_H
#define _LINUX_LIST_H

struct list_head {
	struct list_head *next, *prev;
};

static inline bool __list_add_valid(struct list_head *new,
				struct list_head *prev,
				struct list_head *next)
{
	return true;
}
static inline bool __list_del_entry_valid(struct list_head *entry)
{
	return true;
}

/**
 * INIT_LIST_HEAD - Initialize a list_head structure
 * @list: list_head structure to be initialized.
 *
 * Initializes the list_head to point to itself.  If it is a list header,
 * the result is an empty list.
 */
static inline void INIT_LIST_HEAD(struct list_head *list)
{
	WRITE_ONCE(list->next, list);
	list->prev = list;
}

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_add(struct list_head *new,
			      struct list_head *prev,
			      struct list_head *next)
{
	if (!__list_add_valid(new, prev, next))
		return;

	next->prev = new;
	new->next = next;
	new->prev = prev;
	WRITE_ONCE(prev->next, new);
}

/**
 * list_add - add a new entry
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
[[rc::parameters("pnew : loc", "phead : loc", "next : {option (option type)}")]]
[[rc::args("pnew @ &own<list_node<None>>", "phead @ &own<list_node<next>>")]]
[[rc::ensures("own pnew : list_node<next>", "own phead : list_node<{Some (Some (place pnew))}>")]]
[[rc::trust_me]]
static inline void list_add(struct list_head *new, struct list_head *head)
{
	__list_add(new, head, head->next);
}


/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline void list_add_tail(struct list_head *new, struct list_head *head)
{
	__list_add(new, head->prev, head);
}

/*
 * Delete a list entry by making the prev/next entries
 * point to each other.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_del(struct list_head * prev, struct list_head * next)
{
	next->prev = prev;
	WRITE_ONCE(prev->next, next);
}

static inline void __list_del_entry(struct list_head *entry)
{
	if (!__list_del_entry_valid(entry))
		return;

	__list_del(entry->prev, entry->next);
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
[[rc::parameters("p : loc", "next : {option (option type)}")]]
// TODO: we also need ownership of prev and next
[[rc::args("p @ &own<list_node<next>>")]]
[[rc::ensures("own p : list_node<None>")]]
[[rc::trust_me]]
static inline void list_del_init(struct list_head *entry)
{
	__list_del_entry(entry);
	INIT_LIST_HEAD(entry);
}

/**
 * list_empty - tests whether a list is empty
 * @head: the list to test.
 */
[[rc::parameters("p : loc", "next : {option (option type)}")]]
[[rc::args("p @ &own<list_node<next>>")]]
[[rc::returns("{bool_decide (next = None)} @ boolean<i32>")]]
[[rc::ensures("own p : list_node<next>")]]
[[rc::trust_me]]
static inline int list_empty(const struct list_head *head)
{
	return READ_ONCE(head->next) == head;
}

/**
 * list_entry - get the struct for this entry
 * @ptr:	the &struct list_head pointer.
 * @type:	the type of the struct this is embedded in.
 * @member:	the name of the list_head within the struct.
 */
#define list_entry(ptr, type, member) \
	container_of(ptr, type, member)

/**
 * list_first_entry - get the first element from a list
 * @ptr:	the list head to take the element from.
 * @type:	the type of the struct this is embedded in.
 * @member:	the name of the list_head within the struct.
 *
 * Note, that list is expected to be not empty.
 */
#define list_first_entry(ptr, type, member) \
	list_entry((ptr)->next, type, member)

#endif /* _LINUX_LIST_H */

/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* #include <asm/page.h> */

/* #include <linux/types.h> */

#define HYP_MEMBLOCK_REGIONS 128
struct hyp_memblock_region {
	phys_addr_t start;
	phys_addr_t end;
};
struct [[rc::refined_by("pool : loc", "vmemmap : loc", "vmemmap_len : nat", "refcount : Z", "order : Z",
						"next : {option (option Z)}")]]
       [[rc::immovable]]
       [[rc::typedef("hyp_page : immovable<λ self. ...>")]]
hyp_page {
	[[rc::field("refcount @ int<u32>")]]
	unsigned int refcount;
	[[rc::field("order @ int<u32>")]]
	unsigned int order;
	[[rc::field("&own<place<pool>>")]]
	struct hyp_pool *pool;
	[[rc::field("own_constrained<nonshr_constraint<{hyp_page_to_virt vmemmap self ◁ₗ next @ optionalO (λ _, uninit (PAGE_LAYOUT (Z.shiftl 1 order))) (place (hyp_page_to_virt vmemmap self))}>, list_node<idx_to_node<vmemmap, vmemmap_len, next>>>")]]
	struct list_head node;
};

extern s64 hyp_physvirt_offset;
// TODO: frontend seems to get confused by having both [extern u64 x]
// and [u64 x] in the same file: rc::global does not seem to work anymore
// extern u64 __hyp_vmemmap;
[[rc::parameters("vmemmap : loc")]]
[[rc::global("&shr<place<vmemmap>>")]]
void *__hyp_vmemmap;
#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(virt)	((void *)((phys_addr_t)(virt) - hyp_physvirt_offset))

static inline void *hyp_phys_to_virt(phys_addr_t phys)
{
	return __hyp_va(phys);
}

static inline phys_addr_t hyp_virt_to_phys(void *addr)
{
	return __hyp_pa(addr);
}

#define hyp_phys_to_pfn(phys)	((phys) >> PAGE_SHIFT)
/* #define hyp_phys_to_page_MACRO(phys)	(&hyp_vmemmap[hyp_phys_to_pfn(phys)]) */
#define hyp_phys_to_page_MACRO(phys)	(hyp_vmemmap + hyp_phys_to_pfn(phys))
[[rc::parameters("p : Z", "vmemmap : loc", "pages : {list type}")]]
[[rc::args("p @ int<u64>")]]
[[rc::requires("[initialized \"__hyp_vmemmap\" vmemmap]", "own vmemmap : array<struct_hyp_page, pages>")]]
[[rc::returns("&own<array_ptr<struct_hyp_page, vmemmap, {hyp_phys_to_page vmemmap p}, {length pages}>>")]]
[[rc::ensures("own vmemmap : array<struct_hyp_page, pages>")]]
[[rc::trust_me]]
static inline struct hyp_page * hyp_phys_to_page(phys_addr_t phys) {
	return hyp_phys_to_page_MACRO(phys);
}
#define hyp_virt_to_page(virt)	hyp_phys_to_page(__hyp_pa(virt))

#define hyp_page_to_phys_MACRO(page)  ((phys_addr_t)((page) - hyp_vmemmap) << PAGE_SHIFT)
[[rc::parameters("p : loc", "page : Z", "vmemmap : loc", "len : nat")]]
[[rc::args("p @ &own<array_ptr<struct_hyp_page, vmemmap, page, len>>")]]
[[rc::requires("[initialized \"__hyp_vmemmap\" vmemmap]")]]
[[rc::returns("{hyp_page_to_phys vmemmap page} @ int<u64>")]]
[[rc::ensures("own p : array_ptr<struct_hyp_page, vmemmap, page, len>")]]
[[rc::trust_me]]
static inline phys_addr_t hyp_page_to_phys(struct hyp_page *page) {
	return hyp_page_to_phys_MACRO(page);
}
#define hyp_page_to_virt(page)	__hyp_va(hyp_page_to_phys(page))
#define hyp_page_to_pool(page)	(((struct hyp_page *)page)->pool)

static inline int hyp_page_count(void *addr)
{
	struct hyp_page *p = hyp_virt_to_page(addr);

	return p->refcount;
}

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

struct [[rc::refined_by("heads : {list (option (option Z))}",
						"pages : {list (Z * Z * (option (option Z)))}",
						"npages : nat",
						"vmemmap : loc",
						"range_start : Z", "range_end : Z")]]
       [[rc::immovable]]
       [[rc::typedef("hyp_pool : immovable<λ self. ...>")]]
       [[rc::constraints("[initialized \"__hyp_vmemmap\" vmemmap]")]]
       [[rc::constraints("{length pages = npages}")]]
[[rc::exists("lid : lock_id")]] hyp_pool {
	[[rc::field("own_constrained<nonshr_constraint<{vmemmap ◁ₗ !{ array<struct_hyp_page, {((λ '(ref_count, order, next), (self, vmemmap, npages, ref_count, order, next)) <$> pages) `at_type` hyp_page}> } }>, spinlock<lid>>")]]
	hyp_spinlock_t lock;
	[[rc::field("array<struct_list_head, {(λ h, !{ list_node<idx_to_node<vmemmap, npages, h>> }) <$> heads}>")]]
	struct list_head free_area[HYP_MAX_ORDER + 1];
	[[rc::field("range_start @ int<u64>")]]
	phys_addr_t range_start;
	[[rc::field("range_end @ int<u64>")]]
	phys_addr_t range_end;
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
[[rc::parameters("pool : loc", "pageloc : loc", "page : Z", "vmemmap : loc", "heads : {list (option (option Z))}", "pages : {list (Z * Z * (option (option Z)))}", "npages : nat", "range_start : Z", "range_end : Z", "order : Z")]]
[[rc::args("pool @ &own<{(heads, pages, npages, vmemmap, range_start, range_end)} @ hyp_pool>",
		   "pageloc @ &own<array_ptr<struct_hyp_page, vmemmap, page, npages>>", "order @ int<u32>")]]
[[rc::returns("{0 <= find_buddy vmemmap order page < npages} @ optional<&own<array_ptr<struct_hyp_page, vmemmap, {find_buddy vmemmap order page}, npages>>, null>")]]
[[rc::ensures("own pool : {(heads, pages, npages, vmemmap, range_start, range_end)} @ hyp_pool")]]
[[rc::ensures("own pageloc : array_ptr<struct_hyp_page, vmemmap, page, npages>")]]
[[rc::trust_me]]
static struct hyp_page *__find_buddy(struct hyp_pool *pool, struct hyp_page *p,
				     unsigned int order)
{
	rc_unfold(pool->lock);
	phys_addr_t addr = hyp_page_to_phys(p);

	addr ^= (PAGE_SIZE << order);
	if (addr < pool->range_start || addr >= pool->range_end)
		return NULL;

	return hyp_phys_to_page(addr);
}

[[rc::parameters("pool : loc", "page : Z", "vmemmap : loc", "heads : {list (option (option Z))}",
				 "pages : {list (Z * Z * (option (option Z)))}", "npages : nat",
				 "range_start : Z", "range_end : Z", "order : Z")]]
[[rc::args("pool @ &own<{(heads, pages, npages, vmemmap, range_start, range_end)} @ hyp_pool>",
		   "&own<array_ptr<struct_hyp_page, vmemmap, page, npages>>")]]
[[rc::requires("{0 <= page < npages}")]]
[[rc::requires("{pages !! Z.to_nat page = Some (0, order, None)}")]]
[[rc::requires("[hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ page) ◁ₗ uninit (PAGE_LAYOUT (1 ≪ order))]")]]
[[rc::exists("heads2 : _", "pages2 : _")]]
[[rc::ensures("own pool : {(heads2, pages2, npages, vmemmap, range_start, range_end)} @ hyp_pool")]]
[[rc::trust_me]]
static void __hyp_attach_page(struct hyp_pool *pool,
			      struct hyp_page *p)
{
	rc_unfold(pool->lock);
	unsigned int order = p->order;
	struct hyp_page *buddy;

	p->order = HYP_NO_ORDER;
	[[rc::exists("order : Z", "heads2 : _", "pages2 : _", "page2 : Z")]]
    [[rc::inv_vars("order : order @ int<u32>")]]
	[[rc::inv_vars("pool : pool @ &own<{(heads2, pages2, npages, vmemmap, range_start, range_end)} @ hyp_pool>")]]
	[[rc::inv_vars("p : &own<array_ptr<struct_hyp_page, vmemmap, page2, npages>>")]]
	[[rc::constraints("{0 <= page2 < npages}")]]
	[[rc::constraints("{pages2 !! Z.to_nat page2 = Some (0, HYP_NO_ORDER, None)}")]]
	[[rc::constraints("[hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ page2) ◁ₗ uninit (PAGE_LAYOUT (1 ≪ order))]")]]
	for (; order < HYP_MAX_ORDER; order++) {
		/* Nothing to do if the buddy isn't in a free-list */
		buddy = __find_buddy(pool, p, order);
		rc_unfold(pool->lock);
		// TODO(#30): allow !buddy
		/* if (!buddy || list_empty(&buddy->node) || buddy->order != order) */
		if (buddy == NULL || list_empty(&buddy->node) || buddy->order != order)
			break;

		/* Otherwise, coalesce the buddies and go one level up */
		list_del_init(&buddy->node);
		buddy->order = HYP_NO_ORDER;
		// TODO: the original code generates a weird cerberus error
		/* p = (p < buddy) ? p : buddy; */
		if (p < buddy) {
			p = p;
		} else {
			p = buddy;
		}
	}
	rc_unfold(pool->lock);

	p->order = order;
	// TODO: use list_add_tail, list_node probably should also keep track of the prev pointer
	// list_add_tail(&p->node, &pool->free_area[order]);
	list_add(&p->node, &pool->free_area[order]);
}

void hyp_put_page(void *addr)
{
	struct hyp_page *p = hyp_virt_to_page(addr);
	struct hyp_pool *pool = hyp_page_to_pool(p);

	hyp_spin_lock(&pool->lock);
	if (!p->refcount)
		hyp_panic();
	p->refcount--;
	if (!p->refcount)
		__hyp_attach_page(pool, p);
	hyp_spin_unlock(&pool->lock);
}

void hyp_get_page(void *addr)
{
	struct hyp_page *p = hyp_virt_to_page(addr);
	struct hyp_pool *pool = hyp_page_to_pool(p);

	hyp_spin_lock(&pool->lock);
	p->refcount++;
	hyp_spin_unlock(&pool->lock);
}

/* Extract a page from the buddy tree, at a specific order */
static struct hyp_page *__hyp_extract_page(struct hyp_pool *pool,
					   struct hyp_page *p,
					   unsigned int order)
{
	struct hyp_page *buddy;

	if (p->order == HYP_NO_ORDER || p->order < order)
		return NULL;

	list_del_init(&p->node);

	/* Split the page in two until reaching the requested order */
	while (p->order > order) {
		p->order--;
		buddy = __find_buddy(pool, p, p->order);
		buddy->order = p->order;
		list_add_tail(&buddy->node, &pool->free_area[buddy->order]);
	}

	p->refcount = 1;

	return p;
}

static void clear_hyp_page(struct hyp_page *p)
{
	unsigned long i;

	for (i = 0; i < (1 << p->order); i++)
		clear_page((unsigned char *)hyp_page_to_virt(p) + (i << PAGE_SHIFT));
		// TODO: cerberus does not allow pointer arithmetic on void *
		/* clear_page(hyp_page_to_virt(p) + (i << PAGE_SHIFT)); */
}

static void *__hyp_alloc_pages(struct hyp_pool *pool, gfp_t mask,
			       unsigned int order)
{
	unsigned int i = order;
	struct hyp_page *p;

	/* Look for a high-enough-order page */
	while (i <= HYP_MAX_ORDER && list_empty(&pool->free_area[i]))
		i++;
	if (i > HYP_MAX_ORDER)
		return NULL;

	/* Extract it from the tree at the right order */
	p = list_first_entry(&pool->free_area[i], struct hyp_page, node);
	p = __hyp_extract_page(pool, p, order);

	if (mask & HYP_GFP_ZERO)
		clear_hyp_page(p);

	return p;
}

void *hyp_alloc_pages(struct hyp_pool *pool, gfp_t mask, unsigned int order)
{
	struct hyp_page *p;

	hyp_spin_lock(&pool->lock);
	p = __hyp_alloc_pages(pool, mask, order);
	hyp_spin_unlock(&pool->lock);

	return p ? hyp_page_to_virt(p) : NULL;
}

/* hyp_vmemmap must be backed beforehand */
int hyp_pool_init(struct hyp_pool *pool, phys_addr_t phys,
		  unsigned int nr_pages, unsigned int used_pages)
{
	struct hyp_page *p;
	int i;

	if (phys % PAGE_SIZE)
		return -EINVAL;

	hyp_spin_lock_init(&pool->lock);
	for (i = 0; i <= HYP_MAX_ORDER; i++)
		INIT_LIST_HEAD(&pool->free_area[i]);
	pool->range_start = phys;
	pool->range_end = phys + (nr_pages << PAGE_SHIFT);

	/* Init the vmemmap portion */
	p = hyp_phys_to_page(phys);
	memset(p, 0, sizeof(*p) * nr_pages);
	// TODO: the frontend does not support the comma operator
	/* for (i = 0; i < nr_pages; i++, p++) { */
	for (i = 0; i < nr_pages; i++) {
		p->pool = pool;
		INIT_LIST_HEAD(&p->node);
		p++; // TODO remove after the support for the comma operator is added.
	}

	/* Attach the unused pages to the buddy tree */
	p = hyp_phys_to_page(phys + (used_pages << PAGE_SHIFT));
	// TODO: the frontend does not support the comma operator
	/* for (i = used_pages; i < nr_pages; i++, p++) */
	for (i = used_pages; i < nr_pages; i++) {
		__hyp_attach_page(pool, p);
		p++; // TODO remove after the support for the comma operator is added.
	}

	return 0;
}
