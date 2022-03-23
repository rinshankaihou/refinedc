#include <stddef.h>
#include <refinedc.h>
#include <alloc.h>

#if 0
/* For this example we want to verify the following singly linked
 * list of integers: */

/* A list is represented by a value l of type list_t. l == NULL means
   that the list is empty. Otherwise it points to a struct list_node
   where next contains the tail of the list (note that the type of
   next is equivalent to list_t). */
typedef struct list_node {
  int val;
  struct list_node *next;
} *list_t;

/* append appends k to l. Note that l needs to be a pointer to a list
 * because append is destructive and modified l */
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}
#endif

/* First step is to define the list_t RefinedC type via annotations on
 * the struct. The annotations define the following type:
 * list_t := optional<&own<struct<struct_list_node, int<i32>, list_t>>, null>
 */

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
    /* assert(node1->val == 1); */
  }
}
