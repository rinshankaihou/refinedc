// based on https://github.com/alastairreid/verifast-play/blob/master/src/malloc1.h
// and https://github.com/alastairreid/verifast-play/blob/master/src/malloc1.c

#include <stddef.h>
#include <stdint.h>
#include <refinedc.h>

typedef struct [[rc::ptr_type("freelist_t:{(0 < len)%nat} @ optional<&own<...>>")]]
               [[rc::parameters("entry_size: nat")]]
               [[rc::refined_by("len: nat")]]
               [[rc::size("{ly_with_align entry_size entry_size}")]] freelist {
    [[rc::field("{(len - 1)%nat} @ freelist_t<entry_size>")]]
    struct freelist *next;
} *freelist_t;

struct [[rc::parameters("entry_size: nat")]]
       [[rc::refined_by("len: nat")]]
       [[rc::exists("entries_in_chunk: nat", "entries_in_entry_list: nat", "chunk_p: loc")]]
       [[rc::constraints("{(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size}",
                         "{len = (entries_in_chunk + entries_in_entry_list)%nat}")]] slab {

    // the ordering here is actually important since we first want to look at chunk_size as this determines entries_in_chunk and only later at chunk
    [[rc::field("{entries_in_chunk * entry_size} @ int<size_t>")]]
    size_t chunksize;

    [[rc::field("entry_size @ int<size_t>")]]
    size_t entry_size; // size of objects

    [[rc::field("chunk_p @ &own<uninit<{ly_with_align (entries_in_chunk * entry_size) entry_size}>>")]]
    unsigned char *chunk;

    [[rc::field("entries_in_entry_list @ freelist_t<entry_size>")]]
    freelist_t free; // deallocated objects
};

[[rc::parameters("p : loc", "chunk_p : loc", "n : nat", "entry_size : nat")]]
[[rc::args("p @ &own<uninit<struct_slab>>",
           "chunk_p @ &own<uninit<{ly_with_align (n * entry_size) entry_size}>>",
           "{n * entry_size} @ int<size_t>",
           "entry_size @ int<size_t>")]]
[[rc::requires("{(layout_of struct_freelist) ⊑ ly_with_align entry_size entry_size}")]]
[[rc::ensures("p @ &own<n @ slab<entry_size>>")]]
void slab_init(struct slab *s, unsigned char *p, size_t chunksize, size_t entry_size)
{
    s->chunk = p;
    s->chunksize = chunksize;
    s->entry_size = entry_size;
    s->free = NULL;
}

[[rc::parameters("p : loc", "n : nat", "entry_size : nat")]]
[[rc::args("p @ &own<n @ slab<entry_size>>")]]
[[rc::returns("{(0 < n)%nat} @ optional<&own<uninit<{ly_with_align entry_size entry_size}>>>")]]
[[rc::ensures("p @ &own<{(n - 1)%nat} @ slab<entry_size>>")]]
void* slab_alloc(struct slab *s)
{
    struct freelist *f;
    void* r;
    if (s->free != NULL) {
        f = s->free;
        s->free = f->next;
        r = f;
        return r;
    } else {
        if (s->entry_size > s->chunksize) {
            return NULL;
        } else {
            r = s->chunk;
            s->chunk = s->chunk + s->entry_size;
            s->chunksize = s->chunksize - s->entry_size;
            return r;
        }
    }
}

[[rc::parameters("p : loc", "fp : loc", "n : nat", "entry_size : nat")]]
[[rc::args("p @ &own<n @ slab<entry_size>>", "fp @ &own<uninit<{ly_with_align entry_size entry_size}>>")]]
[[rc::ensures("p @ &own<{(n + 1)%nat} @ slab<entry_size>>")]]
void slab_free(struct slab *s, void* x)
{
    struct freelist* f = x;
    // unfold slab to learn that struct_freelist < entry_size
    rc_unfold(*s);

    f->next = s->free;
    s->free = f;
}
