// SPDX-License-Identifier: GPL-2.0-only
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>

typedef unsigned long long u64;
typedef signed long long s64;
typedef u64 phys_addr_t;
typedef u64 gfp_t;

#define PAGE_SIZE 4096
#define PAGE_SHIFT 12
#define EINVAL 22

#define WRITE_ONCE(a, b) ((a) = (b))
#define READ_ONCE(a) (a)

#define HYP_MAX_ORDER	11U
#define HYP_NO_ORDER	UINT_MAX

#define container_of(ptr, type, member) (type *)( (char *)(ptr) - offsetof(type,member) )

/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _LINUX_LIST_H
#define _LINUX_LIST_H

struct list_head {
	struct list_head *next, *prev;
};

/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */

#define LIST_HEAD_INIT(name) { &(name), &(name) }

#define LIST_HEAD(name) \
	struct list_head name = LIST_HEAD_INIT(name)

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
	/* if (!__list_add_valid(new, prev, next)) */
	if (__list_add_valid(new, prev, next) == (bool)0)
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
	/* if (!__list_del_entry_valid(entry)) */
	if (__list_del_entry_valid(entry) == (bool)0)
		return;

	__list_del(entry->prev, entry->next);
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
static inline void list_del_init(struct list_head *entry)
{
	__list_del_entry(entry);
	INIT_LIST_HEAD(entry);
}

/**
 * list_empty - tests whether a list is empty
 * @head: the list to test.
 */
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

#endif

struct hyp_pool {
	/* nvhe_spinlock_t lock; */
	struct list_head free_area[HYP_MAX_ORDER + 1];
};

/* GFP flags */
#define HYP_GFP_NONE	0
#define HYP_GFP_ZERO	1

#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* #include <asm/page.h> */

/* #include <linux/types.h> */

struct hyp_pool;
struct hyp_page {
	unsigned int order;
	struct hyp_pool *pool;
	int refcount;
	union {
		/* allocated page */
		void *virt;
		/* free page */
		struct list_head node;
	};
	/* Range of 'sibling' pages (donated by the host at the same time) */
	phys_addr_t sibling_range_start;
	phys_addr_t sibling_range_end;
};

extern s64 hyp_physvirt_offset;
extern u64 __hyp_vmemmap;
#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(virt)	(void*)((phys_addr_t)(virt) - hyp_physvirt_offset)

static inline void *hyp_phys_to_virt(phys_addr_t phys)
{
	return __hyp_va(phys);
}

static inline phys_addr_t hyp_virt_to_phys(void* addr)
{
	return __hyp_pa(addr);
}

#define hyp_phys_to_pfn(phys)	((phys) >> PAGE_SHIFT)
#define hyp_phys_to_page(phys)	&hyp_vmemmap[hyp_phys_to_pfn(phys)]
#define hyp_virt_to_page(virt)	hyp_phys_to_page(__hyp_pa(virt))

#define hyp_page_to_phys(page)  ((phys_addr_t)((page) - hyp_vmemmap) << PAGE_SHIFT)
#define hyp_page_to_virt(page)	__hyp_va(hyp_page_to_phys(page))
#define hyp_page_to_pool(page)	((struct hyp_page*)page)->pool

#endif /* __KVM_HYP_MEMORY_H */

// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */

/* #include <asm/kvm_hyp.h> */
/* #include <nvhe/gfp.h> */

u64 __hyp_vmemmap;

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
static struct hyp_page * __find_buddy(struct hyp_pool *pool,
						 struct hyp_page *p,
						 unsigned int order)
{
	phys_addr_t addr = hyp_page_to_phys(p);

	addr ^= (PAGE_SIZE << order);
	if (addr < p->sibling_range_start || addr >= p->sibling_range_end)
		return NULL;

	return hyp_phys_to_page(addr);
}

static void __hyp_attach_page(struct hyp_pool *pool,
					 struct hyp_page *p)
{
	unsigned int order = p->order;
	struct hyp_page *buddy;

	p->order = HYP_NO_ORDER;
	for (;order < HYP_MAX_ORDER; order++) {
		/* Nothing to do if the buddy isn't in a free-list */
		buddy = __find_buddy(pool, p, order);
		if (!buddy || list_empty(&buddy->node) || buddy->order != order)
			break;

		/* Otherwise, coalesce the buddies and go one level up */
		list_del_init(&buddy->node);
		buddy->order = HYP_NO_ORDER;
		if (buddy < p) {
			p = buddy;
		}
		/* p = (p < buddy) ? p : buddy; */
	}

	p->order = order;
	list_add_tail(&p->node, &pool->free_area[order]);
}

void hyp_put_page(void *addr)
{
	struct hyp_page *p = hyp_virt_to_page(addr);
	struct hyp_pool *pool = hyp_page_to_pool(p);

	/* nvhe_spin_lock(&pool->lock); */
	p->refcount--;
	if (!p->refcount)
		__hyp_attach_page(pool, p);
	/* nvhe_spin_unlock(&pool->lock); */
}

void hyp_get_page(void *addr)
{
	struct hyp_page *p = hyp_virt_to_page(addr);
	struct hyp_pool *pool = hyp_page_to_pool(p);

	/* nvhe_spin_lock(&pool->lock); */
	p->refcount++;
	/* nvhe_spin_unlock(&pool->lock); */
}

/* Extract a page from the buddy tree, at a specific order */
static struct hyp_page * __hyp_extract_page(struct hyp_pool *pool,
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

extern void clear_page(void *to);
static void clear_hyp_page(struct hyp_page *p)
{
	unsigned long i;

	/* for (i = 0; i < (1 << p->order); i++) */
	for (i = 0; i < (1UL << p->order); i++)
		clear_page((unsigned char *)hyp_page_to_virt(p) + (i << PAGE_SHIFT));
		/* clear_page(hyp_page_to_virt(p) + (i << PAGE_SHIFT)); */
}

static void * __hyp_alloc_pages(struct hyp_pool *pool, gfp_t mask,
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

void * hyp_alloc_pages(struct hyp_pool *pool, gfp_t mask,
				  unsigned int order)
{
	struct hyp_page *p;

	/* nvhe_spin_lock(&pool->lock); */
	p = __hyp_alloc_pages(pool, mask, order);
	/* nvhe_spin_unlock(&pool->lock); */

	/* return p ? hyp_page_to_virt(p) : NULL; */
	if (p) {
		return hyp_page_to_virt(p);
	} else {
		return NULL;
	}
}
#if 0
/* hyp_vmemmap must be backed beforehand */
int hyp_pool_extend_used(struct hyp_pool *pool, phys_addr_t phys,
				    unsigned int nr_pages,
				    unsigned int used_pages)
{
	phys_addr_t range_end = phys + (nr_pages << PAGE_SHIFT);
	struct hyp_page *p;
	int i;

	if (phys % PAGE_SIZE)
		return -EINVAL;

	/* nvhe_spin_lock(&pool->lock); */

	/* Init the vmemmap portion - XXX can be done lazily ? */
	p = hyp_phys_to_page(phys);
	for (i = 0; i < nr_pages; i++, p++) {
		p->order = 0;
		p->pool = pool;
		p->refcount = 0;
		INIT_LIST_HEAD(&p->node);
		p->sibling_range_start = phys;
		p->sibling_range_end = range_end;
	}

	/* Attach the unused pages to the buddy tree - XXX optimize ? */
	p = hyp_phys_to_page(phys + (used_pages << PAGE_SHIFT));
	for (i = used_pages; i < nr_pages; i++, p++)
		__hyp_attach_page(pool, p);

	/* nvhe_spin_unlock(&pool->lock); */

	return 0;
}
#endif
void hyp_pool_init(struct hyp_pool *pool)
{
	unsigned int i;

	/* nvhe_spin_lock_init(&pool->lock); */
	for (i = 0; i <= HYP_MAX_ORDER; i++)
		INIT_LIST_HEAD(&pool->free_area[i]);
}
