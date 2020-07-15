#include <stdbool.h>
#include "../inc/refinedc.h"
#include "alloc.h"

// In part inspired from the following example from Verifast:
// https://github.com/verifast/verifast/blob/master/examples/sorted_bintree.c

typedef struct [[rc::refined_by("s : {gset Z}")]]
               [[rc::ptr_type("tree_t : {s ≠ ∅} @ optional<&own<...>>")]]
               [[rc::exists("sl : {gset Z}", "sr : {gset Z}", "k : Z")]]
               [[rc::constraints("{s = sl ∪ {[k]} ∪ sr}", "{∀ i, i ∈ sl → i < k}",
                                 "{∀ i, i ∈ sr → k < i}")]]
tree {
  [[rc::field("sl @ tree_t")]]
  struct tree* left;

  [[rc::field("sr @ tree_t")]]
  struct tree* right;

  [[rc::field("k @ int<size_t>")]]
  size_t key;
} *tree_t;

[[rc::returns("{∅} @ tree_t")]]
tree_t empty(){
  return NULL;
}

[[rc::parameters("k : Z")]]
[[rc::args("k @ int<size_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{{[k]}} @ tree_t")]]
 [[rc::tactics("all: try by set_solver.")]]
tree_t init(size_t key){
  struct tree *node = alloc(sizeof(struct tree));
  node->left  = NULL;
  node->key   = key;
  node->right = NULL;
  return node;
}

[[rc::parameters("sl : {gset Z}", "k : Z", "sr : {gset Z}")]]
[[rc::args("sl @ tree_t", "k @ int<size_t>", "sr @ tree_t")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::requires("{∀ i, i ∈ sl → i < k}", "{∀ i, i ∈ sr → k < i}")]]
[[rc::returns("{sl ∪ {[k]} ∪ sr} @ tree_t")]]
 [[rc::tactics("all: try by set_solver.")]]
tree_t node(tree_t left, size_t key, tree_t right){
  struct tree *node = alloc(sizeof(struct tree));
  node->left  = left;
  node->key   = key;
  node->right = right;
  return node;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<tree_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("p @ &own<uninit<LPtr>>")]]
void free_tree(tree_t* t){
  if(*t != NULL){
    free_tree(&((*t)->left));
    free_tree(&((*t)->right));
    free(sizeof(struct tree), *t);
  }
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::returns("{bool_decide (k ∈ s)} @ boolean<bool_it>")]]
 [[rc::tactics("all: try by set_unfold; naive_solver lia.")]]
bool member_rec(tree_t* t, size_t k){
  if(*t == NULL) return false;
  if((*t)->key == k) return true;
  if(k < (*t)->key) return member_rec(&((*t)->left), k);
  return member_rec(&((*t)->right), k);
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::returns("{bool_decide (k ∈ s)} @ boolean<bool_it>")]]
[[rc::ensures("p @ &own<s @ tree_t>")]]
 [[rc::tactics("all: try by set_unfold; naive_solver lia.")]]
bool member(tree_t* t, size_t k){
  tree_t* cur = &*t;

  [[rc::exists("cur_p : loc", "cur_s : {gset Z}")]]
  [[rc::inv_vars("cur : cur_p @ &own<cur_s @ tree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{cur_p ◁ₗ cur_s @ tree_t}, s @ tree_t>>")]]
  [[rc::constraints("{k ∈ s ↔ k ∈ cur_s}")]]
  while(*cur != NULL){
    if((*cur)->key == k) return true;
    if(k < (*cur)->key){
      cur = &((*cur)->left);
    } else {
      cur = &((*cur)->right);
    }
  }
  return false;
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("p @ &own<{{[k]} ∪ s} @ tree_t>")]]
 [[rc::tactics("all: try by set_unfold; solve_goal.")]]
void insert_rec(tree_t* t, size_t k){
  if(*t == NULL){
    *t = node(NULL, k, NULL);
  } else {
    if((*t)->key == k) return;
    if(k < (*t)->key){
      insert_rec(&((*t)->left), k);
    } else {
      insert_rec(&((*t)->right), k);
    }
  }
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("p @ &own<{{[k]} ∪ s} @ tree_t>")]]
 [[rc::tactics("all: try by set_unfold; solve_goal.")]]
void insert(tree_t* t, size_t k){
  tree_t* cur = &*t;

  [[rc::exists("cur_p : loc", "cur_s : {gset Z}")]]
  [[rc::inv_vars("cur : cur_p @ &own<cur_s @ tree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{cur_p ◁ₗ ({[k]} ∪ cur_s) @ tree_t}, {{[k]} ∪ s} @ tree_t>>")]]
  while(*cur != NULL){
    if((*cur)->key == k) return;
    if(k < (*cur)->key){
      cur = &((*cur)->left);
    } else {
      cur = &((*cur)->right);
    }
  }

  *cur = node(NULL, k, NULL);
}

[[rc::parameters("p : loc", "s : {gset Z}")]]
[[rc::args("p @ &own<s @ tree_t>")]]
[[rc::requires("{s ≠ ∅}")]]
[[rc::exists("m : Z")]]
[[rc::returns("m @ int<size_t>")]]
[[rc::ensures("{m ∈ s}", "{∀ i, i ∈ s → i ≤ m}")]]
[[rc::ensures("p @ &own<s @ tree_t>")]]
 [[rc::tactics("all: by set_unfold; naive_solver lia.")]]
size_t tree_max(tree_t* t){
  if((*t)->right == NULL) {
    return (*t)->key;
  }
  rc_unfold((*t)->right->key);
  return tree_max(&((*t)->right));
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ tree_t>", "k @ int<size_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("p @ &own<{s ∖ {[k]}} @ tree_t>")]]
 [[rc::tactics("all: try apply Z.le_neq.")]]
 [[rc::tactics("all: try (rewrite difference_union_L !difference_union_distr_l_L !difference_diag_L !difference_disjoint_L; move: (H0 x2) (H1 x2); clear -H9).")]]
 [[rc::tactics("all: try by set_unfold; naive_solver lia.")]]
void remove(tree_t* t, size_t k){
  tree_t tmp;
  size_t m;
  if(*t == NULL) {
    return;
  }

  if(k == (*t)->key) {
    if((*t)->left != NULL){
      rc_unfold((*t)->left->key);
      m = tree_max(&(*t)->left);
      remove(&(*t)->left, m);
      (*t)->key = m;
    } else {
      tmp = (*t)->right;
      free(sizeof(struct tree), *t);
      *t = tmp;
    }
  } else if(k < (*t)->key){
    remove(&(*t)->left, k);
  } else {
    remove(&(*t)->right, k);
  }
}

[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{0} @ int<i32>")]]
int main(){
  tree_t t = empty();
  t = init(3);

  //assert(!member(&t, 2)); // FIXME cast missing?

  insert(&t, 2);

  assert(member(&t, 2));
  assert(member(&t, 3));

  remove(&t, 3);
  //assert(!member(t, 3); // FIXME cast missing?

  insert(&t, 3);
  assert(member(&t, 2));

  remove(&t, 3);
  //assert(!member(t, 3); // FIXME cast missing?

  free_tree(&t);

  return 0;
}
