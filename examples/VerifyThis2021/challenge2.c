#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <refinedc.h>

//#define size size_rec
#define size size_iter

//@rc::import defs from refinedc.examples.VerifyThis2021.challenge2

typedef struct
[[rc::refined_by("t: {tree Z}")]]
[[rc::ptr_type("tree_t : {node_data t} @ optionalO<λ (l,k,r). &own<...>>")]]
Node {
  [[rc::field("k @ int<i32>")]] int data;
  [[rc::field("l @ tree_t")]]   struct Node *prev; // left subtree
  [[rc::field("r @ tree_t")]]   struct Node *next; // right subtree
} *Ref;

// Since the RefinedC frontend at the moment does not allow defining two different types via annotations on the frontend, we use a hack to define a second type via a rc::ptr_type on a dummy struct.
struct [[rc::refined_by("l: {list Z}")]]
       [[rc::ptr_type("list_t : {maybe2 cons l} @ optionalO<λ (k, l). &own<struct<struct_Node, k @ int<i32>, uninit<void*>, l @ list_t>>>")]]
dummy { [[rc::field("int<i32>")]] int a; };


[[rc::parameters("v: val", "l: {list Z}")]]
[[rc::args("at_value<v, l @ list_t>")]]
[[rc::requires("{length l ≤ max_int size_t}")]]
[[rc::returns("{length l} @ int<size_t>")]]
[[rc::ensures("v : l @ list_t")]]
size_t size_rec(Ref head){
  if(head == NULL) return 0;
  return size_rec(head->next) + 1;
}

[[rc::parameters("v: val", "l: {list Z}")]]
[[rc::args("at_value<v, l @ list_t>")]]
[[rc::requires("{length l ≤ max_int size_t}")]]
[[rc::returns("{length l} @ int<size_t>")]]
[[rc::ensures("v : l @ list_t")]]
size_t size_iter(Ref head){
  size_t len = 0;

  [[rc::exists("v2: val", "l1: {list Z}")]]
  [[rc::inv_vars("head: own_constrained<nonshr_constraint<{v2 ◁ᵥ l1 @ list_t}>, value<PtrOp,v2>>")]]
  [[rc::inv_vars("len : {length l - length l1} @ int<size_t>")]]
  [[rc::constraints("v : wand_val<void*, {v2 ◁ᵥ l1 @ list_t}, l @ list_t>")]]
  while (head != NULL) {
    head = head->next;
    len += 1;
  }

  return len;
}

[[rc::parameters("l: {list Z}", "p: loc", "n: nat")]]
[[rc::args("l @ list_t", "p @ &own<uninit<void*>>", "n @ int<size_t>")]]
[[rc::requires("{n ≤ length l}")]]
[[rc::exists("t: {tree Z}", "l_rest: {list Z}")]]
[[rc::returns("t @ tree_t")]]
[[rc::ensures("own p: l_rest @ list_t")]]
[[rc::ensures("{list_tree_eq_aux n l t l_rest}")]]
[[rc::lemmas("list_tree_eq_aux_Node_Z")]]
[[rc::lemmas("list_tree_eq_aux_is_Some")]]
[[rc::lemmas("list_tree_eq_aux_le")]]
Ref dll_to_bst_rec(Ref head, Ref *right, size_t n){
  Ref root, left, temp;

  if(n == 0){
    *right = head;
    return NULL;
  }

  left = dll_to_bst_rec(head, &root, n / 2);
  root->prev = left;

  temp = dll_to_bst_rec(root->next, right, n - n/2 - 1);
  root->next = temp;

  return root;
}

[[rc::parameters("l: {list Z}")]]
[[rc::args("l @ list_t")]]
[[rc::requires("{length l ≤ max_int size_t}")]]
[[rc::exists("t: {tree Z}")]]
[[rc::returns("t @ tree_t")]]
[[rc::ensures("{list_tree_eq l t}")]]
[[rc::lemmas("tree_list_eq_full_length")]]
Ref dll_to_bst(Ref head){
  size_t n = size(head);
  Ref right;
  return dll_to_bst_rec(head, &right, n);
}
