/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Based on arch/arm/include/asm/page.h
 *
 * Copyright (C) 1995-2003 Russell King
 * Copyright (C) 2017 ARM Ltd.
 */
#ifndef __ASM_PAGE_DEF_H
#define __ASM_PAGE_DEF_H

#define PAGE_SHIFT 12
#define PAGE_SIZE  4096
#define PAGE_MASK  (~(PAGE_SIZE-1))

//@rc::inlined
//@Definition PAGE_SHIFT := (12).
//@Definition PAGE_SIZE := (4096).
//@
//@Definition PAGES (n : nat) : layout :=
//@  ly_with_align (n * Z.to_nat PAGE_SIZE) (Z.to_nat PAGE_SIZE).
//@
//@Notation PAGE := (PAGES 1).
//@rc::end

#endif /* __ASM_PAGE_DEF_H */
