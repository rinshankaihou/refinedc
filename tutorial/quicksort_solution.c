#include <stddef.h>

//@rc::import list_proofs from refinedc.tutorial.quicksort_solution

typedef struct
  [[rc::refined_by("xs : {list Z}")]]
  [[rc::ptr_type("list_t : {xs <> []} @ optional<&own<...>, null>")]]
  [[rc::exists("y : Z", "ys : {list Z}")]]
  [[rc::constraints("{xs = y :: ys}")]]
list_node {
  [[rc::field("y @ int<i32>")]]
  int val;
  [[rc::field("ys @ list_t")]]
  struct list_node *next;
} *list_t;

// xs @ list_t := {xs <> []} @ optional<&own<∃ y ys,
//     struct struct_list_node [ y @ int<i32>, ys @ list_t]
//       & {xs = y :: ys}
//     >, null>

[[rc::parameters("p : loc", "xs : {list Z}", "ys : {list Z}")]]
[[rc::args("p @ &own<xs @ list_t>", "ys @ list_t")]]
[[rc::ensures("p @ &own<{xs ++ ys} @ list_t>")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

// TODO: iterative version of append

[[rc::parameters("p : loc", "xs : {list Z}", "z : Z")]]
[[rc::args("p @ &own<xs @ list_t>", "z @ int<i32>")]]
[[rc::returns("{filter (λ v, z <= v) xs} @ list_t")]]
[[rc::ensures("p @ &own<{filter (λ v, v < z) xs} @ list_t>")]]
[[rc::tactics("all: try by rewrite filter_cons; solve_goal.")]]
list_t partition(list_t *l, int pivot) {
  if(*l == NULL) {
    return NULL;
  } else {
    list_t rest = partition(&(*l)->next, pivot);
    list_t head = *l;
    if(pivot <= (*l)->val) {
      *l = (*l)->next;
      head->next = rest;
      return head;
    } else {
      return rest;
    }
  }
}

[[rc::parameters  ("list_l : {list Z}", "l : loc")]]
[[rc::args        ("l @ &own<list_l @ list_t>")]]
[[rc::exists      ("sorted_l : {list Z}")]]
[[rc::ensures     ("l @ &own<sorted_l @ list_t>", "{Permutation list_l sorted_l}", "{Sorted Z.le sorted_l}")]]
[[rc::tactics     ("all: try (eapply sorted_append_middle_el => //; [ apply _ | | ]; last first).")]]
[[rc::tactics     ("all: repeat list_perm_subst; eauto using filter_permutation, Forall_filter with lia.")]]
void quicksort(list_t* l) {
  if(*l == NULL) {
    return;
  } else {
    int pivot = (*l)->val;
    list_t higher = partition(l, pivot);
    quicksort(&higher);
    quicksort(l);
    append(l, higher);
  }
}
