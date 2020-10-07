#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <refinedc.h>
#include "alloc.h"
#include "list.h"

/**
    Note that one does not need to give an explicit reason why the
    recursion is well founded. Instead RefinedC internally uses
    stepindexing to make this recursive definition well founded. In
    practice this is invisible to the user.
*/

typedef struct [[rc::refined_by("l: {list type}")]]
               [[rc::ptr_type("list_t : {maybe2 cons l} @ optionalO<λ (ty, l). &own<...>>")]]
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
[[rc::returns("{bool_decide (l = [])} @ boolean<bool_it>")]]
[[rc::ensures("p @ &own<l @ list_t>")]]
bool is_empty (list_t *l) {
    return *l == NULL;
}

[[rc::parameters("l : {list type}", "ty : type")]]
[[rc::args("l @ list_t", "&own<ty>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{ty :: l} @ list_t")]]
list_t push (list_t p, void *e) {
    struct list *node = alloc(sizeof(struct list));
    node->head = e;
    node->tail = p;
    return node;
}

[[rc::parameters("l : {list type}", "p : loc")]]
[[rc::args("p @ &own<l @ list_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{maybe2 cons l} @ optionalO<λ (ty, l). &own<ty>>")]]
[[rc::ensures("p @ &own<{tail l} @ list_t>")]]
void *pop (list_t *p) {
  if (*p == NULL) {
      return NULL;
  }
  struct list *node = *p;
  void *ret = node->head;
  *p = node->tail;
  free(sizeof(struct list), node);
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

[[rc::parameters("p : loc", "l1 : {list type}", "l2 : {list type}")]]
[[rc::args("p @ &own<l1 @ list_t>", "l2 @ list_t")]]
[[rc::ensures("p @ &own<{l1 ++ l2} @ list_t>")]]
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
[[rc::returns("b @ boolean<bool_it>")]]
[[rc::ensures("p @ &own<{l `at_type` int size_t} @ list_t>", "{b ↔ n ∈ l}")]]
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
            return 1;
        }

        prev = &cur->tail;
    }
    return 0;
}

 [[rc::tactics("all: try by set_unfold; refined_solver.")]]
void test() {
    list_t list = init();
    size_t *elem1 = alloc(sizeof(size_t));
    size_t *elem2 = alloc(sizeof(size_t));
    size_t *elem3 = alloc(sizeof(size_t));

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

    free(sizeof(size_t), elem1);
    free(sizeof(size_t), elem2);
    free(sizeof(size_t), elem3);
}

[[rc::parameters("p : loc", "l1 : {list type}", "l2 : {list type}")]]
[[rc::args("l1 @ list_t", "p @ &own<l2 @ list_t>")]]
[[rc::ensures("p @ &own<{(rev l1) ++ l2} @ list_t>")]]
void rev_append(list_t l1, list_t *l2) {
  list_t cur = l1;
  list_t cur_tail;

  [[rc::exists("l1_prefix : {list type}", "l1_suffix : {list type}")]]
  [[rc::exists("cur_l2 : {list type}")]]
  [[rc::inv_vars("cur : l1_suffix @ list_t")]]
  [[rc::inv_vars("l2 : p @ &own<cur_l2 @ list_t>")]]
  [[rc::inv_vars("l1 : uninit<LPtr>")]]
  [[rc::constraints("{cur_l2 = l1_prefix ++ l2}")]]
  [[rc::constraints("{l1 = rev l1_prefix ++ l1_suffix}")]]
  while(cur != NULL) {
    cur_tail = cur->tail;
    cur->tail = *l2;
    *l2 = cur;
    cur = cur_tail;
  }
}