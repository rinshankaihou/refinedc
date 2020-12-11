// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */
#include <stddef.h>

#define PAGE_SIZE 4096
#define PAGE_SHIFT 12

//@rc::inlined Definition PAGE_SIZE : N := 4096.
//@rc::inlined Definition PAGE_LAYOUT := ly_with_align (N.to_nat PAGE_SIZE) (N.to_nat PAGE_SIZE).

static unsigned long base;
static unsigned long end;
static unsigned long cur;
unsigned long hyp_early_alloc_nr_pages(void)
{
	return (cur - base) >> PAGE_SHIFT;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<PAGE_LAYOUT>>")]]
[[rc::ensures("p @ &own<zeroed<PAGE_LAYOUT>>")]]
extern void clear_page(void *to);

void * hyp_early_alloc_page(void *arg)
{
	unsigned long ret = cur;
	cur += PAGE_SIZE;
	if (cur > end) {
		cur = ret;
		return NULL;
	}
	clear_page((void*)ret);
	return (void *)ret;
}

void hyp_early_alloc_init(unsigned long virt, unsigned long size)
{
	base = virt;
	end = virt + size;
	cur = virt;

	/* hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page; */
	/* hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt; */
	/* hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys; */
}

/*
  Modified version with size instead of end pointer:
*/


static unsigned char *base1;
static unsigned long size1;
static unsigned char * cur1;

/* unsigned long hyp_early_alloc_nr_pages(void) */
/* { */
/* 	return (cur - base) >> PAGE_SHIFT; */
/* } */

[[rc::parameters("n : nat")]]
[[rc::args("ptr")]]
[[rc::requires("global cur1 : &own<uninit<{ly_set_size PAGE_LAYOUT n}>>")]]
[[rc::requires("global size1 : n @ int<u64>")]]
[[rc::exists("m : nat")]]
[[rc::returns("optional<&own<zeroed<PAGE_LAYOUT>>, null>")]]
[[rc::ensures("global size1 : m @ int<u64>")]]
[[rc::ensures("global cur1 : &own<uninit<{ly_set_size PAGE_LAYOUT m}>>")]]
void * hyp_early_alloc_page1(void *arg)
{
	if (size1 <= (unsigned long) PAGE_SIZE) {
		return NULL;
	}

	unsigned char *ret = cur1;
	cur1 += PAGE_SIZE;
	size1 -= PAGE_SIZE;
	clear_page((void*)ret);
	return (void *)ret;
}

[[rc::parameters("n : nat")]]
[[rc::requires("global cur1  : uninit<LPtr>")]]
[[rc::requires("global size1 : uninit<u64>")]]
[[rc::requires("global base1 : uninit<LPtr>")]]
[[rc::args("&own<uninit<{ly_set_size PAGE_LAYOUT n}>>", "n @ int<u64>")]]
[[rc::exists("m : nat")]]
[[rc::ensures("global size1 : m @ int<u64>")]]
[[rc::ensures("global cur1  : &own<uninit<{ly_set_size PAGE_LAYOUT m}>>")]]
[[rc::ensures("global base1 : uninit<LPtr>")]]
void hyp_early_alloc_init1(unsigned char *virt, unsigned long size)
{
	base1 = virt;
	size1 = size;
	cur1 = virt;

	/* hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page; */
	/* hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt; */
	/* hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys; */
}
