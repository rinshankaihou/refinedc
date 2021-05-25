#include <stddef.h>
#include <refinedc.h>
#include <alloc.h>

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

void test() {
  struct list_node * node1 = alloc(sizeof(struct list_node));
  node1->val = 1; node1->next = NULL;
  struct list_node * node2 = alloc(sizeof(struct list_node));
  node2->val = 2; node2->next = NULL;
  append(&node1, node2);
  if(node1 != NULL) {
    assert(node1->val == 1);
  }
}
