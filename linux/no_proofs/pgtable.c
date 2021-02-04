/*

Inductive pgtable : Type :=
| PT_leaf address attrs
| PT_table address (children : list pgtable)

*/

struct kvm_pgtable [[rc::refined_by("pgd : pagetable", ...)]] {
	u32					ia_bits;
	u32					start_level;
	[[rc::field("&own<pgd @ kvm_pte_t>")]]
	kvm_pte_t				*pgd;
	struct kvm_pgtable_mm_ops		*mm_ops;

	/* Stage-2 only */
	struct kvm_s2_mmu			*mmu;
};

enum kvm_pgtable_walk_flags {
	KVM_PGTABLE_WALK_LEAF			= BIT(0),
	KVM_PGTABLE_WALK_TABLE_PRE		= BIT(1),
	KVM_PGTABLE_WALK_TABLE_POST		= BIT(2),
};

typedef int (*kvm_pgtable_visitor_fn_t)(u64 addr, u64 end, u32 level,
					kvm_pte_t *ptep,
					enum kvm_pgtable_walk_flags flag,
					void * const arg);
/*
visitor_fn_t P arg_ty Q := {fn(
   ∀ (addr, end, level, ptep, pg, flag, arg) : (Z * Z * Z * loc * pgtable * walk_flag * loc);
   addr @ int<u64>, end @ int<u64>, level @ int<u32>,
   ptep @ &own<pg @ kvm_pte_t>, {[flag]} @ kvm_pgtable_walk_flags, arg @ arg_ty<addr, end, level, pg, flag>;
   P<addr, end, level, pg, flag> →
   ∃ i : Z, i @ int<i32>; Q<i, addr, end, level, pg, flag>

with additional constraints about arg_ty, P and Q (basically that you
can transform Q into P and arg_ty as required by the code)

or you have some kind of functional program as the precondition that
matches the structure of the code and produces and consumes the right
resources at the right times?!

 */
/**
 * struct kvm_pgtable_walker - Hook into a page-table walk.
 * @cb:		Callback function to invoke during the walk.
 * @arg:	Argument passed to the callback function.
 * @flags:	Bitwise-OR of flags to identify the entry types on which to
 *		invoke the callback function.
 */
struct kvm_pgtable_walker {
	[[rc::field("function_ptr<visitor_fn_t>")]]
	const kvm_pgtable_visitor_fn_t		cb;
	void * const				arg;
	const enum kvm_pgtable_walk_flags	flags;
};

static int kvm_pgtable_visitor_cb(struct kvm_pgtable_walk_data *data, u64 addr,
				  u32 level, kvm_pte_t *ptep,
				  enum kvm_pgtable_walk_flags flag)
{
	struct kvm_pgtable_walker *walker = data->walker;
	return walker->cb(addr, data->end, level, ptep, flag, walker->arg);
}

static int __kvm_pgtable_walk(struct kvm_pgtable_walk_data *data,
			      kvm_pte_t *pgtable, u32 level);

static inline int __kvm_pgtable_visit(struct kvm_pgtable_walk_data *data,
				      kvm_pte_t *ptep, u32 level)
{
	int ret = 0;
	u64 addr = data->addr;
	kvm_pte_t *childp, pte = *ptep;
	bool table = kvm_pte_table(pte, level);
	enum kvm_pgtable_walk_flags flags = data->walker->flags;

	if (table && (flags & KVM_PGTABLE_WALK_TABLE_PRE)) {
		ret = kvm_pgtable_visitor_cb(data, addr, level, ptep,
					     KVM_PGTABLE_WALK_TABLE_PRE);
	}

	if (!table && (flags & KVM_PGTABLE_WALK_LEAF)) {
		ret = kvm_pgtable_visitor_cb(data, addr, level, ptep,
					     KVM_PGTABLE_WALK_LEAF);
		pte = *ptep;
		table = kvm_pte_table(pte, level);
	}

	if (ret)
		goto out;

	if (!table) {
		data->addr += kvm_granule_size(level);
		goto out;
	}

	childp = kvm_pte_follow(pte, data->pgt->mm_ops);
	ret = __kvm_pgtable_walk(data, childp, level + 1);
	if (ret)
		goto out;

	if (flags & KVM_PGTABLE_WALK_TABLE_POST) {
		ret = kvm_pgtable_visitor_cb(data, addr, level, ptep,
					     KVM_PGTABLE_WALK_TABLE_POST);
	}

out:
	return ret;
}

static int __kvm_pgtable_walk(struct kvm_pgtable_walk_data *data,
			      kvm_pte_t *pgtable, u32 level)
{
	u32 idx;
	int ret = 0;

	if (WARN_ON_ONCE(level >= KVM_PGTABLE_MAX_LEVELS))
		return -EINVAL;

	for (idx = kvm_pgtable_idx(data, level); idx < PTRS_PER_PTE; ++idx) {
		kvm_pte_t *ptep = &pgtable[idx];

		if (data->addr >= data->end)
			break;

		ret = __kvm_pgtable_visit(data, ptep, level);
		if (ret)
			break;
	}

	return ret;
}

static int _kvm_pgtable_walk(struct kvm_pgtable_walk_data *data)
{
	u32 idx;
	int ret = 0;
	struct kvm_pgtable *pgt = data->pgt;
	u64 limit = BIT(pgt->ia_bits);

	if (data->addr > limit || data->end > limit)
		return -ERANGE;

	if (!pgt->pgd)
		return -EINVAL;

	for (idx = kvm_pgd_page_idx(data); data->addr < data->end; ++idx) {
		kvm_pte_t *ptep = &pgt->pgd[idx * PTRS_PER_PTE];

		ret = __kvm_pgtable_walk(data, ptep, pgt->start_level);
		if (ret)
			break;
	}

	return ret;
}

int kvm_pgtable_walk(struct kvm_pgtable *pgt, u64 addr, u64 size,
		     struct kvm_pgtable_walker *walker)
{
	struct kvm_pgtable_walk_data walk_data = {
		.pgt	= pgt,
		.addr	= ALIGN_DOWN(addr, PAGE_SIZE),
		.end	= PAGE_ALIGN(walk_data.addr + size),
		.walker	= walker,
	};

	return _kvm_pgtable_walk(&walk_data);
}
