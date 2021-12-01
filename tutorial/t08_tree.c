#include <stdbool.h>
#include <refinedc.h>
#include "alloc.h"

//@rc::import t08_tree_extra from refinedc.tutorial.t08_tree

// In part inspired from the following example from Verifast:
// https://github.com/verifast/verifast/blob/master/examples/sorted_bintree.c

typedef struct [[rc::refined_by("t: {tree Z}")]]
               [[rc::ptr_type("tree_t : {node_data t} @ optionalO<λ (l,k,r). &own<...>>")]]
tree {
  [[rc::field("l @ tree_t")]]
  struct tree* left;

  [[rc::field("r @ tree_t")]]
  struct tree* right;

  [[rc::field("k @ int<i32>")]]
  int key;
} *tree_t;

[[rc::returns("leaf @ tree_t")]]
tree_t empty(){
  return NULL;
}

[[rc::parameters("k : Z")]]
[[rc::args("k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{node leaf k leaf} @ tree_t")]]
tree_t init(int key){
  struct tree *node = alloc(sizeof(struct tree));
  node->left  = NULL;
  node->key   = key;
  node->right = NULL;
  return node;
}

[[rc::parameters("l : {tree Z}", "k : Z", "r : {tree Z}")]]
[[rc::args("l @ tree_t", "k @ int<i32>", "r @ tree_t")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{node l k r} @ tree_t")]]
tree_t node(tree_t left, int key, tree_t right){
  struct tree *node = alloc(sizeof(struct tree));
  node->left  = left;
  node->key   = key;
  node->right = right;
  return node;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<tree_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : uninit<void*>")]]
void free_tree(tree_t* t){
  if(*t != NULL){
    free_tree(&((*t)->left));
    free_tree(&((*t)->right));
    free(sizeof(struct tree), *t);
  }
}

[[rc::parameters("p : loc", "t : {tree Z}", "k : Z")]]
[[rc::args("p @ &own<t @ tree_t>", "k @ int<i32>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : t @ tree_t", "{b ↔ tree_member k t}")]]
bool member_rec(tree_t* t, int k){
  if(*t == NULL) return false;
  if((*t)->key == k) return true;
  if(k < (*t)->key) return member_rec(&((*t)->left), k);
  return member_rec(&((*t)->right), k);
}

[[rc::parameters("p : loc", "t : {tree Z}", "k : Z")]]
[[rc::args("p @ &own<t @ tree_t>", "k @ int<i32>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : t @ tree_t", "{b ↔ tree_member k t}")]]
bool member(tree_t* t, int k){
  tree_t* cur = &*t;

  [[rc::exists("p_cur : loc", "branch : {tree Z}")]]
  [[rc::inv_vars("cur : p_cur @ &own<branch @ tree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{p_cur ◁ₗ branch @ tree_t}, t @ tree_t>>")]]
  [[rc::constraints("{tree_member k t ↔ tree_member k branch}")]]
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

[[rc::parameters("p : loc", "t : {tree Z}", "k : Z")]]
[[rc::args("p @ &own<t @ tree_t>", "k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : {tree_insert k t} @ tree_t")]]
void insert_rec(tree_t* t, int k){
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

[[rc::parameters("p : loc", "t : {tree Z}", "k : Z")]]
[[rc::args("p @ &own<t @ tree_t>", "k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : {tree_insert k t} @ tree_t")]]
void insert(tree_t* t, int k){
  tree_t* cur = &*t;

  [[rc::exists("p_cur : loc", "branch : {tree Z}")]]
  [[rc::inv_vars("cur : p_cur @ &own<branch @ tree_t>")]]
  [[rc::inv_vars("t : p @ &own<wand<{p_cur ◁ₗ (tree_insert k branch) @ tree_t}, {tree_insert k t} @ tree_t>>")]]
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

[[rc::parameters("p : loc", "l : {tree Z}", "k : Z", "r : {tree Z}")]]
[[rc::args("p @ &own<{node l k r} @ tree_t>")]]
[[rc::exists("res : Z")]]
[[rc::returns("res @ int<i32>")]]
[[rc::ensures("{tree_max (node l k r) = Some res}")]]
[[rc::ensures("own p : {node l k r} @ tree_t")]]
int tree_max(tree_t* t){
    if((*t)->right == NULL) {
        return (*t)->key;
    }
    rc_unfold((*t)->right->key);
    return tree_max(&((*t)->right));
}

[[rc::parameters("p : loc", "t : {tree Z}", "k : Z")]]
[[rc::args("p @ &own<t @ tree_t>", "k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : {tree_remove k t} @ tree_t")]]
 [[rc::tactics("all: try by case_bool_decide => //; simplify_eq.")]]
void remove(tree_t* t, int k){
  tree_t tmp;
  int m;
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

struct [[rc::refined_by("s: {gset Z}")]]
       [[rc::ptr_type("stree_t : ∃ t. t @ tree_t & {tree_rel s t}")]]
dummy { [[rc::field("int<i32>")]] int a; };

[[rc::returns("{∅} @ stree_t")]]
 [[rc::lemmas("LeafRel")]]
tree_t sempty(){
  return empty();
}

[[rc::parameters("k : Z")]]
[[rc::args("k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{{[k]}} @ stree_t")]]
 [[rc::tactics("all: try by apply: NodeRel; try apply LeafRel; set_solver.")]]
tree_t sinit(int key){
  return init(key);
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<stree_t>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : uninit<void*>")]]
void sfree_tree(tree_t* t){
  rc_unfold_once(*t);
  free_tree(t);
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ stree_t>", "k @ int<i32>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : s @ stree_t", "{b ↔ k ∈ s}")]]
 [[rc::tactics("all: try by etrans; [done|]; symmetry; apply tree_rel_member.")]]
bool smember(tree_t* t, int k){
  rc_unfold_once(*t);
  return member(t, k);
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ stree_t>", "k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : {{[k]} ∪ s} @ stree_t")]]
 [[rc::lemmas("tree_rel_insert")]]
void sinsert(tree_t* t, int k){
  rc_unfold_once(*t);
  insert(t, k);
}

[[rc::parameters("p : loc", "s : {gset Z}", "k : Z")]]
[[rc::args("p @ &own<s @ stree_t>", "k @ int<i32>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::ensures("own p : {s ∖ {[k]}} @ stree_t")]]
 [[rc::lemmas("tree_rel_remove")]]
void sremove(tree_t* t, int k){
  rc_unfold_once(*t);
  remove(t, k);
}


[[rc::requires("[alloc_initialized]")]]
[[rc::returns("{0} @ int<i32>")]]
int main(){
  tree_t t = sempty();
  t = sinit(3);

  //assert(!member(&t, 2)); // FIXME cast missing?

  sinsert(&t, 2);

  assert(smember(&t, 2));
  assert(smember(&t, 3));

  sremove(&t, 3);
  //assert(!member(t, 3); // FIXME cast missing?

  sinsert(&t, 3);
  assert(smember(&t, 2));

  sremove(&t, 3);
  //assert(!member(t, 3); // FIXME cast missing?

  sfree_tree(&t);

  return 0;
}
