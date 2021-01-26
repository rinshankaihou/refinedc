#include <stddef.h>
#include <refinedc.h>
#include <alloc.h>

typedef struct
[[rc::ptr_type("list_t : optional<&own<...>, null>")]]
list_node {
  [[rc::field("int<i32>")]]
  int val;
  [[rc::field("list_t")]]
  struct list_node *next;
} *list_t;

[[rc::args("&own<list_t>", "list_t")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

/* [[rc::requires("[alloc_initialized]")]] */
void test() {
  struct list_node * node1 = alloc(sizeof(struct list_node));
  node1->val = 1; node1->next = NULL;
  struct list_node * node2 = alloc(sizeof(struct list_node));
  node2->val = 2; node2->next = NULL;
  append(&node1, node2);
  if(node1 != NULL) {
    assert(node1->val == 1);
  }
  /* assert(node1->next->val == 2); */
  /* free(sizeof(struct list_node), node1->next); */
  /* free(sizeof(struct list_node), node1); */
}