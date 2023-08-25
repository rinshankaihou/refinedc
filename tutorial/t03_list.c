#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <refinedc.h>
#include "talloc.h"
#include "list.h"

/**
    Note that one does not need to give an explicit reason why the
    recursion is well founded. Instead RefinedC internally uses
    stepindexing to make this recursive definition well founded. In
    practice this is invisible to the user.
*/

typedef struct [[rc::refined_by("l: {list type}")]]
               [[rc::typedef("list_t : {maybe2 cons l} @ optionalO<λ (ty, l). &own<...>, null>")]]
list {
    [[rc::field("&own<ty>")]]
    void *head;

    [[rc::field("l @ list_t")]]
    struct list *tail;
} *list_t;

[[rc::returns("{[]} @ list_t")]]
list_t init () {
    return NULL;
}

[[rc::parameters("p : loc", "l : {list type}")]]
[[rc::args("p @ &own<l @ list_t>")]]
[[rc::returns("{bool_decide (l = [])} @ builtin_boolean")]]
[[rc::ensures("own p : l @ list_t")]]
bool is_empty (list_t *l) {
    return *l == NULL;
}

[[rc::parameters("l : {list type}", "ty : type")]]
[[rc::args("l @ list_t", "&own<ty>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::returns("{ty :: l} @ list_t")]]
list_t push (list_t p, void *e) {
    struct list *node = talloc(sizeof(struct list));
    node->head = e;
    node->tail = p;
    return node;
}

[[rc::parameters("l : {list type}", "p : loc")]]
[[rc::args("p @ &own<l @ list_t>")]]
[[rc::requires("[talloc_initialized]")]]
[[rc::returns("{maybe2 cons l} @ optionalO<λ (ty, l). &own<ty>>")]]
[[rc::ensures("own p : {tail l} @ list_t")]]
void *pop (list_t *p) {
  if (*p == NULL) {
      return NULL;
  }
  struct list *node = *p;
  void *ret = node->head;
  *p = node->tail;
  tfree(sizeof(struct list), node);
  return ret;
}

[[rc::parameters("l : {list type}")]]
[[rc::args("l @ list_t")]]
[[rc::returns("{rev l} @ list_t")]]
list_t reverse (list_t p) {
    list_t w, t;
    w = NULL;
    [[rc::exists("l1 : {list type}", "l2 : {list type}")]]
    [[rc::inv_vars("w : l1 @ list_t", "p : l2 @ list_t")]]
    [[rc::constraints("{l = rev l1 ++ l2}")]]
    while (p != NULL) {
        t = p->tail;
        p->tail = w;
        w = p;
        p = t;
    }
    return w;
}

[[rc::parameters("p : loc", "l : {list type}")]]
[[rc::args("p @ &own<l @ list_t>")]]
[[rc::requires("{length l ≤ max_int size_t}")]]
[[rc::returns("{length l} @ int<size_t>")]]
[[rc::ensures("own p : l @ list_t")]]
size_t length (list_t *p) {
  size_t len = 0;
  [[rc::exists("q : loc", "l1 : {list type}")]]
  [[rc::inv_vars("p : q @ &own<l1 @ list_t>", "len : {length l - length l1} @ int<size_t>")]]
  [[rc::constraints("own p : wand<{q ◁ₗ l1 @ list_t}, l @ list_t>")]]
  while (*p != NULL) {
    p = &(*p)->tail;
    len += 1;
  }
  return len;
}

[[rc::parameters("v : val", "l : {list type}")]]
[[rc::args("at_value<v, l @ list_t>")]]
[[rc::requires("{length l ≤ max_int size_t}")]]
[[rc::returns("{length l} @ int<size_t>")]]
[[rc::ensures("v : l @ list_t")]]
size_t length_val_rec (list_t p) {
  if(p == NULL) {
    return 0;
  }
  return length_val_rec(p->tail) + 1;
}

[[rc::parameters("v : val", "l : {list type}")]]
[[rc::args("at_value<v, l @ list_t>")]]
[[rc::requires("{length l ≤ max_int size_t}")]]
[[rc::returns("{length l} @ int<size_t>")]]
[[rc::ensures("v : l @ list_t")]]
size_t length_val (list_t p) {
  size_t len = 0;
  [[rc::exists("v2 : val", "l1 : {list type}")]]
  [[rc::inv_vars("p : at_value<v2, l1 @ list_t>", "len : {length l - length l1} @ int<size_t>")]]
  [[rc::constraints("v : wand_val<void*, {v2 ◁ᵥ l1 @ list_t}, l @ list_t>")]]
  while (p != NULL) {
    p = p->tail;
    len += 1;
  }
  return len;
}

[[rc::parameters("p : loc", "l1 : {list type}", "l2 : {list type}")]]
[[rc::args("p @ &own<l1 @ list_t>", "l2 @ list_t")]]
[[rc::ensures("own p : {l1 ++ l2} @ list_t")]]
void append(list_t *l1, list_t l2) {
  list_t *end = l1;
  [[rc::exists("pl : loc", "l1_suffix : {list type}")]]
  [[rc::inv_vars("end : pl @ &own<l1_suffix @ list_t>")]]
  [[rc::inv_vars("l1 : p @ &own<wand<{pl ◁ₗ (l1_suffix ++ l2) @ list_t}, {l1 ++ l2} @ list_t>>")]]
  while(*end != NULL){
    end = &((*end)->tail);
  }
  *end = l2;
}

[[rc::parameters("l : {list Z}", "p : loc", "n : Z" )]]
[[rc::args("p @ &own<{l `at_type` int size_t} @ list_t>", "n @ int<size_t>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : {l `at_type` int size_t} @ list_t", "{b ↔ n ∈ l}")]]
 [[rc::tactics("all: try set_unfold; refined_solver.")]]
bool member (list_t *p, size_t k) {
    list_t *prev = p;
    [[rc::exists("l1 : {list Z}", "pc : loc")]]
    [[rc::inv_vars("prev : pc @ &own<{l1 `at_type` int size_t} @ list_t>")]]
    [[rc::inv_vars("p : p @ &own<wand<{pc ◁ₗ (l1 `at_type` int size_t) @ list_t}, {l `at_type` int size_t} @ list_t>>")]]
    [[rc::constraints("{n ∈ l ↔ n ∈ l1}")]]
    while(*prev != NULL) {
        list_t cur = *prev;

        size_t *head = cur->head;
        if(*head == k) {
            return true;
        }

        prev = &cur->tail;
    }
    return false;
}

 [[rc::tactics("all: try by set_unfold; refined_solver.")]]
void test() {
    list_t list = init();
    size_t *elem1 = talloc(sizeof(size_t));
    size_t *elem2 = talloc(sizeof(size_t));
    size_t *elem3 = talloc(sizeof(size_t));

    assert(is_empty(&list));

    *elem1 = 1;
    *elem2 = 2;
    *elem3 = 3;

    list = push(list, elem1);
    list = push(list, elem2);
    list = push(list, elem3);

    assert(member(&list, 1));

    list = reverse(list);

    assert(member(&list, 1));

    elem1 = pop(&list);
    elem2 = pop(&list);
    elem3 = pop(&list);

    assert(is_empty(&list));

    assert(*elem1 == (size_t)1);
    assert(*elem2 == (size_t)2);
    assert(*elem3 == (size_t)3);

    tfree(sizeof(size_t), elem1);
    tfree(sizeof(size_t), elem2);
    tfree(sizeof(size_t), elem3);
}

[[rc::parameters("p : loc", "l1 : {list type}", "l2 : {list type}")]]
[[rc::args("l1 @ list_t", "p @ &own<l2 @ list_t>")]]
[[rc::ensures("own p : {(rev l1) ++ l2} @ list_t")]]
void rev_append(list_t l1, list_t *l2) {
  list_t cur = l1;
  list_t cur_tail;

  [[rc::exists("l1_prefix : {list type}", "l1_suffix : {list type}")]]
  [[rc::exists("cur_l2 : {list type}")]]
  [[rc::inv_vars("cur : l1_suffix @ list_t")]]
  [[rc::inv_vars("l2 : p @ &own<cur_l2 @ list_t>")]]
  [[rc::inv_vars("l1 : uninit<void*>")]]
  [[rc::constraints("{cur_l2 = l1_prefix ++ l2}")]]
  [[rc::constraints("{l1 = rev l1_prefix ++ l1_suffix}")]]
  while(cur != NULL) {
    cur_tail = cur->tail;
    cur->tail = *l2;
    *l2 = cur;
    cur = cur_tail;
  }
}
