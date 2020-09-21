#pragma once

#include <stddef.h>
#include <stdbool.h>

// Order of the B-trees (maximum number of children for a node). Note that the
// implementation could be made more generic by letting clients choose what is
// the order of a B-tree at its creation. To do this, the representation needs
// to be changed to use a flexible array member. And this feature is not (yet)
// very well supported by Cerberus.
#define ORDER 5

//@rc::import btree_extra from refinedc.examples.btree
//@rc::inlined
//@(* B-tree order, should match the defined ORDER in C. *)
//@Definition ORDER : nat := 5.
//@rc::end

// Representation of B-trees and definition of the corresponding RefinedC type
// [btree_t], refined by a tuple [r] of type [btree_rfmt], containing (mainly)
// a functional map [br_map r].  The refinement also contains other properties
// of the B-tree, like its height or the minimum and maximum keys it may store
// (for internal nodes).
typedef struct
[[rc::refined_by("r : btree_rfmt")]]
// A B-tree is either a leaf (NULL) or a node (owned pointer to struct btree).
[[rc::ptr_type(
  "btree_t : ∃ (n,ks,vs,cs) : {nat * list Z * list type * list btree_rfmt}. "
  "({br_map r ≠ ∅} @ optional<&own<...>>) "
  "& {btree_invariant ORDER r n ks vs cs}"
)]]
// In the node (i.e., non-NULL), the following variables are used: the natural
// number n gives the number of keys stored in the node, the list ks gives the
// keys stored in the node, and vs gives the corresponding values. The list cs
// gives the expected refinement for each child node.
[[rc::constraints("{length ks = n}", "{length vs = n}", "{length cs = S n}")]]
btree {
  [[rc::field("n @ int<i32>")]]
  int nb_keys;

  [[rc::field("array_p<i32, {ks `at_type` int i32}, {(ORDER-1-n)%nat}>")]]
  int keys[ORDER - 1];

  [[rc::field("array_p<LPtr, {(λ ty, (&own ty : type)) <$> vs}, {(ORDER-1-n)%nat}>")]]
  void* vals[ORDER - 1];

  [[rc::field("guarded<array_p<LPtr, {cs `at_type` !{btree_t<>}}, {(ORDER-1-n)%nat}>>")]]
  struct btree* children[ORDER];

  [[rc::field("{br_height r} @ int<i32>")]]
  int height;
}* btree_t;

// Create a new, empty B-tree.
[[rc::requires("[alloc_initialized]")]]
[[rc::returns("&own<{BRroot 0%nat ∅} @ btree_t>")]]
btree_t* new_btree();

// De-allocates the memory used by a B-tree.
[[rc::requires("[alloc_initialized]")]]
[[rc::args("&own<btree_t>")]]
void free_btree(btree_t* t);

// Test if the key k is mapped in the B-tree t.
[[rc::parameters("p : loc", "h : nat", "m : {gmap Z type}", "k : Z")]]
[[rc::args("p @ &own<{BRroot h m} @ btree_t>", "k @ int<i32>")]]
[[rc::returns("{bool_decide (m !! k ≠ None)} @ boolean<bool_it>")]]
[[rc::ensures("p @ &own<{BRroot h m} @ btree_t>")]]
bool btree_member(btree_t* t, int k);

// Find the value associated to the key k in the B-tree t. If the key k is not
// mapped then NULL is returned, otherwise a pointer to the value is returned.
[[rc::parameters("p : loc", "h : nat", "m : {gmap Z type}", "k : Z")]]
[[rc::args("p @ &own<{BRroot h m} @ btree_t>", "k @ int<i32>")]]
[[rc::exists("v : loc")]]
[[rc::returns("{m !! k} @ optionalO<λ ty. v @ &own<ty>>")]]
[[rc::ensures("p @ &own<{BRroot h (make_sp v k m)} @ btree_t>")]]
void** btree_find(btree_t* t, int k);

// Insert the key k with value v in the B-tree t. If the key is already mapped
// then its value is simply updated.
[[rc::parameters("p : loc", "h : nat", "m : {gmap Z type}", "k : Z")]]
[[rc::parameters("v : loc", "ty : type")]]
[[rc::args("p @ &own<{BRroot h m} @ btree_t>")]]
[[rc::args("k @ int<i32>", "v @ &own<ty>")]]
[[rc::requires("[alloc_initialized]")]]
[[rc::exists("new_h : nat")]]
[[rc::ensures("p @ &own<{BRroot new_h (<[k := ty]> m)} @ btree_t>")]]
void btree_insert(btree_t* t, int k, void* v);
