#include <refinedc.h>
#include <stddef.h>
#include <stdbool.h>

typedef struct [[rc::refined_by("l: {list type}")]]
               [[rc::ptr_type("list_t : {maybe2 cons l} @ optionalO<λ (ty, l). &own<...>>")]] list {
    [[rc::field("&own<ty>")]]
    void *head;

    [[rc::field("l @ list_t")]]
    struct list *tail;
} *list_t;

[[rc::returns("{[]} @ list_t")]]
list_t init () {
    return NULL;
}

[[rc::parameters("l : {list type}", "ty : type")]]
[[rc::args("l @ list_t", "&own<ty>", "&own<uninit<struct_list>>")]]
[[rc::returns("{ty :: l} @ list_t")]]
list_t push (list_t p, void *e, struct list *node) {
    node->head = e;
    node->tail = p;
    return node;
}

[[rc::parameters("l : {list type}", "p : loc")]]
[[rc::args("p @ &own<{l} @ list_t>")]]
[[rc::returns("{maybe2 cons l} @ optionalO<λ (ty, l). &own<ty>>")]]
[[rc::ensures("own p : {tail l} @ list_t")]]
void *pop (list_t *p) {
  if (*p == NULL) {
      return NULL;
  }
  void *ret = (*p)->head;
  *p = (*p)->tail;
  return ret;
}

[[rc::parameters("l : {list Z}", "p : loc", "n : Z" )]]
[[rc::args("p @ &own<{l `at_type` int size_t} @ list_t>", "n @ int<size_t>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : {l `at_type` int size_t} @ list_t", "{b ↔ n ∈ l}")]]
[[rc::tactics("all: try set_solver.")]]
bool member_rec (list_t *p, size_t k) {
  if (*p == NULL) {
      return 0;
  }
  size_t *head = (*p)->head;
  if (*head == k) {
      return 1;
  }
  return member_rec(&(*p)->tail, k);
}

[[rc::parameters("l : {list Z}", "p : loc", "n : Z" )]]
[[rc::args("p @ &own<{l `at_type` int size_t} @ list_t>", "n @ int<size_t>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : {l `at_type` int size_t} @ list_t", "{b ↔ n ∈ l}")]]
[[rc::tactics("all: try set_solver.")]]
bool member (list_t *p, size_t k) {
    list_t *prev = &*p;
    [[rc::exists("l1 : {list Z}", "pc : loc")]]
    [[rc::inv_vars(
          "prev : pc @ &own<{l1 `at_type` int size_t} @ list_t>",
          "p : p @ &own<wand<{pc ◁ₗ (l1 `at_type` int size_t) @ list_t}, {l `at_type` int size_t} @ list_t>>")]]
    [[rc::constraints("{n ∈ l ↔ n ∈ l1}")]]
    while(*prev != NULL) {
        list_t cur = *prev;

        size_t *head = cur->head;
        if(*head == k) {
            return 1;
        }

        prev = &cur->tail;
    }
    return 0;
}

[[rc::ensures("True")]]
void test() {
    struct list local1_node, local2_node;
    void *local2; list_t **local3; int *local4;
    list_t list = init();
    int local1 = 0;
    list = push(list, &local1, &local1_node);
    local2 = &list;
    list = push(list, &local2, &local2_node);
    local3 = pop(&list);
    local4 = pop(&**local3);
    assert(*local4 == 0);

    [[rc::exists("l1 :loc", "l2:loc", "l3:loc", "l4:loc")]]
    [[rc::inv_vars("local1 : place<l1>", "local1_node : place<l2>", "local2 : place<l3>", "local2_node : place<l4>")]]
    while(1);
}

// from https://www.cs.princeton.edu/~appel/vc/Verif_reverse.html
[[rc::parameters("l : {list type}")]]
[[rc::args("l @ list_t")]]
[[rc::returns("{rev l} @ list_t")]]
struct list *reverse (struct list *p) {
  struct list *w, *t, *v;
  w = NULL;
  v = p;
  [[rc::exists("l1 : {list type}", "l2 : {list type}")]]
  [[rc::inv_vars("w : l1 @ list_t", "v : l2 @ list_t", "p : uninit<void*>")]]
  [[rc::constraints("{l = rev l1 ++ l2}")]]
  while (v != NULL) {
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}

[[rc::parameters("l : {list type}")]]
[[rc::args("l @ list_t")]]
[[rc::returns("l @ list_t")]]
struct list * forward (struct list *p) {

  struct list **prev = &p;
  [[rc::exists("l1 : {list type}", "pc : loc")]]
  [[rc::inv_vars(
        "prev : pc @ &own<l1 @ list_t>",
        "p : wand<{pc ◁ₗ l1 @ list_t}, l @ list_t>")]]
  while (*prev != NULL) {
      struct list *cur = *prev;

      prev = &cur->tail;
  }
  return p;
}


// hip sleek
// smallfoot space invader
// Thomas Wies
// grasshopper

/* a -> b -> c -> d */
/*      ^    ^ */
/*      prev cur */
/* a -> c */
