#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include <spinlock.h>
#include "alloc_internal.h"

 [[rc::global("alloc_state")]]
static struct alloc_state allocator_state;

void *alloc(size_t size) {

  [[rc::constraints("[initialized \"allocator_state\" ()]")]]
  while(1) {
    sl_lock(&allocator_state.lock);
    rc_unlock(allocator_state.data);


    alloc_entry_t *prev = &allocator_state.data;
    [[rc::block]]
    [[rc::exists("pc : loc")]]
    [[rc::inv_vars("prev : pc @ &own<alloc_entry_t>")]]
    [[rc::constraints("[allocator_state at{struct_alloc_state}ₗ \"data\" ◁ₗ wand (pc ◁ₗ alloc_entry_t) alloc_entry_t]")]]
    while(*prev != NULL) {
      alloc_entry_t cur = *prev;

      if(cur->size == size) {
        *prev = cur->next;
        rc_unfold(*prev);
        sl_unlock(&allocator_state.lock);
        return cur;
      }
      if(cur->size >= size + sizeof(struct alloc_entry)) {
        cur->size -= size;
        void *ret = ((unsigned char*)cur + cur->size);
        rc_unfold(*prev);
        sl_unlock(&allocator_state.lock);
        return ret;
      }

      prev = &cur->next;
    }

    rc_unfold(*prev);
    sl_unlock(&allocator_state.lock);
  }

}

 [[rc::tactics("all: try by rewrite ?Nat2Z.inj_mul ?Z2Nat.id //; apply Z.divide_factor_r.")]]
void free(size_t size, void *ptr) {
  if (size < sizeof(struct alloc_entry)) {
    // Too small to add to the list
    return;
  }

  struct alloc_entry *entry = ptr;
  entry->size = size;

  sl_lock(&allocator_state.lock);
  rc_unlock(allocator_state.data);

  entry->next = allocator_state.data;
  allocator_state.data = entry;

  sl_unlock(&allocator_state.lock);
}

void init_alloc() {
  sl_init(&allocator_state.lock);
  allocator_state.data = NULL;

  // TODO: add a real subtyping annotation such that this hack is not neccesary
  [[rc::constraints("allocator_state @ &own<alloc_state>")]]
  while(0){};

  rc_share(allocator_state);
}

 [[rc::tactics("all: try by rewrite /layout_wf ?Nat2Z.inj_mul ?Z2Nat.id //; repeat apply Z.divide_mul_r.")]]
void *alloc_array(size_t size, size_t n) {
  return alloc(n * size);
}

 [[rc::tactics("all: try by rewrite /layout_wf ?Nat2Z.inj_mul ?Z2Nat.id //; repeat apply Z.divide_mul_r.")]]
void free_array(size_t size, size_t n, void *ptr) {
  free(n * size, ptr);
}
