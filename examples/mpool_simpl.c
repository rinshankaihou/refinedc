#define NULL (void*)0
#include <refinedc.h>

//@rc::inlined Definition ENTRY_LAYOUT := {| ly_size := 16%nat; ly_align_log := 3%nat |}.

struct [[rc::size("ENTRY_LAYOUT")]]
       [[rc::refined_by("n : nat")]] mpool_entry {
    [[rc::field("{(0 < n)%nat} @ optional<&own<{(n - 1)%nat} @ mpool_entry>>")]]
    struct mpool_entry *next;
};

struct [[rc::refined_by("n : nat")]] mpool {
    [[rc::field("{(0 < n)%nat} @ optional<&own<{(n - 1)%nat} @ mpool_entry>>")]]
    struct mpool_entry *entry_list;
};

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<uninit<struct_mpool>>")]]
[[rc::ensures("p @ &own<{0%nat} @ mpool>")]]
void mpool_init(struct mpool *p) {
    p->entry_list = NULL;
}

[[rc::parameters("p : loc", "n : nat")]]
[[rc::args("p @ &own<n @ mpool>")]]
[[rc::returns("{(0 < n)%nat} @ optional<&own<uninit<ENTRY_LAYOUT>>>")]]
[[rc::ensures("p @ &own<{(n - 1)%nat} @ mpool>")]]
void *mpool_get(struct mpool *p) {
    if (p->entry_list == NULL) {
        return NULL;
    }
    struct mpool_entry *entry = p->entry_list;
    p->entry_list = entry->next;
    return entry;
}

[[rc::parameters("p : loc", "n : nat")]]
[[rc::args("p @ &own<n @ mpool>", "&own<uninit<ENTRY_LAYOUT>>")]]
[[rc::ensures("p @ &own<{(n + 1)%nat} @ mpool>")]]
void mpool_put(struct mpool *p, void *ptr) {
    // ptr : &own<uninit<ENTRY_LAYOUT>>
    struct mpool_entry *e = ptr;
    // e: &own<uninit<ENTRY_LAYOUT>>

    // e: &own<padded<uninit<struct_mpool_entry>, struct_mpool_entry, ENTRY_LAYOUT>>
    // e: &own<padded<struct<struct_mpool_entry, [uninit LPtr]>, struct_mpool_entry, ENTRY_LAYOUT>>
    // p: &own<struct<struct_mpool, [{n > 0} @ optional<&own<{n - 1} @ mpool_entry>>]>>
    e->next = p->entry_list;
    // e: &own<padded<struct<struct_mpool_entry, [{n > 0} @ optional<&own<{n - 1} @ mpool_entry>>]>, struct_mpool_entry, ENTRY_LAYOUT>>
    // p: &own<struct<struct_mpool, [uninit<LPtr>]>>
    p->entry_list = e;
    // p: &own<struct<struct_mpool, [&own<padded<struct<struct_mpool_entry, [{n > 0} @ optional<&own<{n - 1} @ mpool_entry>>]>, struct_mpool_entry, ENTRY_LAYOUT>>]>>
}

void* e1, *e2;
[[rc::requires("[global_with_type \"e1\" Own (uninit ENTRY_LAYOUT)]",
               "[global_with_type \"e2\" Own (uninit ENTRY_LAYOUT)]")]]
int main(void) {
    struct mpool p;
    void * p1, *p2;
    mpool_init(&p);
    mpool_put(&p, &e1);
    mpool_put(&p, &e2);
    p1 = mpool_get(&p);
    assert(p1 != NULL);
    p2 = mpool_get(&p);
    assert(p2 != NULL);
}

/*
struct [padded to page size]
       [logical represented by a number n (number of pages linked to by this entry)] mpool_entry {
    [if n > 0, next points to an mpool_entry with n-1 pages, otherwise next is NULL]
    struct mpool_entry *next;
};

struct [logical represented by a number n (the number of pages in this mpool)] mpool {
    [if n > 0, entry_list points to an mpool_entry with n pages, otherwise entry_list is NULL]
    struct mpool_entry *entry_list;
};

[first argument: a pointer p to uninitialized memory of the size of an mpool]
[logically returns: ownership of p, which now points to an (initialized) mpool with 0 pages]
void mpool_init(struct mpool *p) {
    p->entry_list = NULL;
}

[first argument: a pointer p to an mpool with n pages]
[returns: if n > 0, returns an owned pointer to a pages, otherwise returns NULL]
[logically returns: ownership of p, which now points to an mpool with n-1 (bounded at 0) pages ]
void *mpool_get(struct mpool *p) {
    if (p->entry_list == NULL) {
        return NULL;
    }
    struct mpool_entry *entry = p->entry_list;
    p->entry_list = entry->next;
    return entry;
}

[first argument: a pointer p to an mpool with n pages]
[second argument: a pointer to uninitialized memory with page size]
[logically returns: ownership of p, which now points to an mpool with n+1 pages ]
void mpool_put(struct mpool *p, void *ptr) {
    struct mpool_entry *e = ptr;
    e->next = p->entry_list;
    p->entry_list = e;
}

 */
