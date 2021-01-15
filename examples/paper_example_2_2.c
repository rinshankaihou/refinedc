// Example of Section 2.2.

#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include <spinlock.h>

// NOTE: alignment constraint hidden in a coercion.

//@rc::inlined
//@Definition layout_of_nat : nat → layout := ly_set_size struct_chunk.
//@Coercion layout_of_nat : nat >-> layout.
//@
//@Close Scope Z.
//@rc::end

typedef struct
[[rc::refined_by("s: {gmultiset nat}")]]
[[rc::ptr_type("chunks_t : {s ≠ ∅} @ optional<&own<...>, null>")]]
[[rc::exists  ("n : nat", "tail : {gmultiset nat}")]]
[[rc::size    ("n")]]
[[rc::constraints("{s = {[n]} ⊎ tail}",
                  "{∀ k, k ∈ tail → n ≤ k}")]]
chunk {
  [[rc::field("n @ int<size_t>")]] size_t size;
  [[rc::field("tail @ chunks_t")]] struct chunk* next;
}* chunks_t;

[[rc::parameters("s : {gmultiset nat}", "p : loc", "q : loc", "n : nat")]]
[[rc::args      ("p @ &own<s @ chunks_t>", "q @ &own<uninit<n>>",
                 "n @ int<size_t>")]]
[[rc::requires  ("{sizeof struct_chunk ≤ n}")]]
[[rc::ensures   ("own p : {{[n]} ⊎ s} @ chunks_t")]]
[[rc::tactics   ("all: multiset_solver.")]]
void free(chunks_t* list, void *data, size_t size) {
  chunks_t *cur = list;
  [[rc::exists  ("cp : loc", "cs : {gmultiset nat}")]]
  [[rc::inv_vars("cur : cp @ &own<cs @ chunks_t>")]]
  [[rc::inv_vars("list : p @ &own<"
                   "wand<{cp ◁ₗ ({[n]} ⊎ cs) @ chunks_t}, "
                   "{{[n]} ⊎ s} @ chunks_t>>")]]
  while(*cur != NULL) {
    if(size <= (*cur)->size) break;
    cur = &(*cur)->next;
  }
  chunks_t entry = data;
  entry->size = size;
  entry->next = *cur;
  *cur = entry;
}
