#include <stddef.h>

/* Exercise: Quicksort

  1) Add refinement annotations for list_t. Use the refinement unit.

  2) Verify a Rust-like spec for append using the list_t type. Ensure that no ownership gets lost.

  3) Change the refinement of list_t to list Z and update append.

  4) Write a spec for partition and verify it.
     The Coq filter function on lists will be helpful.
*/

typedef struct
list_node {
  int val;
  struct list_node *next;
} *list_t;

void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

list_t partition(list_t *l, int pivot) {
  if(*l == NULL) {
    return NULL;
  } else {
    list_t rest = partition(&(*l)->next, pivot);
    list_t head = *l;
    if((*l)->val <= pivot) {
      *l = (*l)->next;
      head->next = rest;
      return head;
    } else {
      return rest;
    }
  }
}
