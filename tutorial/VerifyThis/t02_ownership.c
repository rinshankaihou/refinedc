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

/* Now we can use the list_t type to specify the arguments of
 * append: */

[[rc::args("&own<list_t>", "list_t")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

/* So far this looks good. What if we try to use append? */

// [[rc::requires("[alloc_initialized]")]] // comment in this line to enable typechecking
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

/* There is an error! We cannot use node1 after calling append. The
 * problem is that append does not give back the ownership of its
 * first argument. This can be fixed by adding an rc::ensures clause
 * that gives back the ownership of the pointer passed for the
 * first argument. */

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<list_t>", "list_t")]]
[[rc::ensures("own p : list_t")]]
void append_2(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append_2(&(*l)->next, k);
  }
}

/* Now the test function typechecks! */

[[rc::requires("[alloc_initialized]")]]
void test_2() {
  struct list_node * node1 = alloc(sizeof(struct list_node));
  node1->val = 1; node1->next = NULL;
  struct list_node * node2 = alloc(sizeof(struct list_node));
  node2->val = 2; node2->next = NULL;

  append_2(&node1, node2);
  if(node1 != NULL) {
    // assert(node1->val == 1); // try commenting in this line
  }
}

/* But the assert fails because the specification of append does not
 * guarantee anything about the values of the list. Continue with
 * t03_ownership_and_refinements.c to see how to fix this. */
