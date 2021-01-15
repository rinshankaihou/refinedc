From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [tree_t]. *)
  Definition tree_t_rec : ((tree Z) -d> typeO) → ((tree Z) -d> typeO) := (λ self t,
    ((node_data t) @ (optionalO (λ patt__,
      let l := patt__.1.1 in
      let k := patt__.1.2 in
      let r := patt__.2 in
      &own (
        struct struct_tree [@{type}
          (guarded ("tree_t_0") (apply_dfun self (l))) ;
          (guarded ("tree_t_1") (apply_dfun self (r))) ;
          (k @ (int (i32)))
        ]
      )
    ) null))
  )%I.
  Typeclasses Opaque tree_t_rec.

  Global Instance tree_t_rec_ne : Contractive tree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition tree_t : rtype := {|
    rty_type := (tree Z);
    rty r__ := fixp tree_t_rec r__
  |}.

  Lemma tree_t_unfold (t : tree Z) :
    (t @ tree_t)%I ≡@{type} (
      ((node_data t) @ (optionalO (λ patt__,
        let l := patt__.1.1 in
        let k := patt__.1.2 in
        let r := patt__.2 in
        &own (
          struct struct_tree [@{type}
            (guarded "tree_t_0" (l @ tree_t)) ;
            (guarded "tree_t_1" (r @ tree_t)) ;
            (k @ (int (i32)))
          ]
        )
      ) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance tree_t_rmovable : RMovable tree_t :=
    {| rmovable 't := movable_eq _ _ (tree_t_unfold t) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance tree_t_simplify_hyp_place_inst l_ β_ (t : tree Z) :
    SimplifyHypPlace l_ β_ (t @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (tree_t_unfold _)).
  Global Instance tree_t_simplify_goal_place_inst l_ β_ (t : tree Z) :
    SimplifyGoalPlace l_ β_ (t @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (tree_t_unfold _)).

  Global Program Instance tree_t_simplify_hyp_val_inst v_ (t : tree Z) :
    SimplifyHypVal v_ (t @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (tree_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance tree_t_simplify_goal_val_inst v_ (t : tree Z) :
    SimplifyGoalVal v_ (t @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (tree_t_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [stree_t]. *)
  Definition stree_t_rec : ((gset Z) -d> typeO) → ((gset Z) -d> typeO) := (λ self s,
    (tyexists (λ t, constrained (t @ (tree_t)) ⌜tree_rel s t⌝))
  )%I.
  Typeclasses Opaque stree_t_rec.

  Global Instance stree_t_rec_ne : Contractive stree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition stree_t : rtype := {|
    rty_type := (gset Z);
    rty r__ := fixp stree_t_rec r__
  |}.

  Lemma stree_t_unfold (s : gset Z) :
    (s @ stree_t)%I ≡@{type} (
      (tyexists (λ t, constrained (t @ (tree_t)) ⌜tree_rel s t⌝))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance stree_t_rmovable : RMovable stree_t :=
    {| rmovable 's := movable_eq _ _ (stree_t_unfold s) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance stree_t_simplify_hyp_place_inst l_ β_ (s : gset Z) :
    SimplifyHypPlace l_ β_ (s @ stree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (stree_t_unfold _)).
  Global Instance stree_t_simplify_goal_place_inst l_ β_ (s : gset Z) :
    SimplifyGoalPlace l_ β_ (s @ stree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (stree_t_unfold _)).

  Global Program Instance stree_t_simplify_hyp_val_inst v_ (s : gset Z) :
    SimplifyHypVal v_ (s @ stree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (stree_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance stree_t_simplify_goal_val_inst v_ (s : gset Z) :
    SimplifyGoalVal v_ (s @ stree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (stree_t_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ size : nat; (size @ (int (size_t))); ⌜size + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (uninit (Layout size 3))); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ size : nat; (size @ (int (size_t))), (&own (uninit (Layout size 3))); (alloc_initialized) ∗ ⌜(8 | size)⌝)
      → ∃ () : (), (void); True.

  (* Specifications for function [alloc_array]. *)
  Definition type_of_alloc_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))); ⌜size * n + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); True.

  (* Specifications for function [free_array]. *)
  Definition type_of_free_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); ⌜size * n ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (void); True.

  (* Specifications for function [empty]. *)
  Definition type_of_empty :=
    fn(∀ () : (); True) → ∃ () : (), (leaf @ (tree_t)); True.

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ k : Z; (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), ((node leaf k leaf) @ (tree_t)); True.

  (* Specifications for function [node]. *)
  Definition type_of_node :=
    fn(∀ (l, k, r) : (tree Z) * Z * (tree Z); (l @ (tree_t)), (k @ (int (i32))), (r @ (tree_t)); (alloc_initialized))
      → ∃ () : (), ((node l k r) @ (tree_t)); True.

  (* Specifications for function [free_tree]. *)
  Definition type_of_free_tree :=
    fn(∀ p : loc; (p @ (&own (tree_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (uninit (void*))).

  (* Specifications for function [member_rec]. *)
  Definition type_of_member_rec :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (p ◁ₗ (t @ (tree_t))) ∗ ⌜b ↔ tree_member k t⌝.

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (p ◁ₗ (t @ (tree_t))) ∗ ⌜b ↔ tree_member k t⌝.

  (* Specifications for function [insert_rec]. *)
  Definition type_of_insert_rec :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tree_insert k t) @ (tree_t))).

  (* Specifications for function [insert]. *)
  Definition type_of_insert :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tree_insert k t) @ (tree_t))).

  (* Specifications for function [tree_max]. *)
  Definition type_of_tree_max :=
    fn(∀ (p, l, k, r) : loc * (tree Z) * Z * (tree Z); (p @ (&own ((node l k r) @ (tree_t)))); True)
      → ∃ res : Z, (res @ (int (i32))); ⌜tree_max (node l k r) = Some res⌝ ∗ (p ◁ₗ ((node l k r) @ (tree_t))).

  (* Specifications for function [remove]. *)
  Definition type_of_remove :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tree_remove k t) @ (tree_t))).

  (* Specifications for function [sempty]. *)
  Definition type_of_sempty :=
    fn(∀ () : (); True) → ∃ () : (), ((∅) @ (stree_t)); True.

  (* Specifications for function [sinit]. *)
  Definition type_of_sinit :=
    fn(∀ k : Z; (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), (({[k]}) @ (stree_t)); True.

  (* Specifications for function [sfree_tree]. *)
  Definition type_of_sfree_tree :=
    fn(∀ p : loc; (p @ (&own (stree_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (uninit (void*))).

  (* Specifications for function [smember]. *)
  Definition type_of_smember :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (stree_t)))), (k @ (int (i32))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (p ◁ₗ (s @ (stree_t))) ∗ ⌜b ↔ k ∈ s⌝.

  (* Specifications for function [sinsert]. *)
  Definition type_of_sinsert :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (stree_t)))), (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (({[k]} ∪ s) @ (stree_t))).

  (* Specifications for function [sremove]. *)
  Definition type_of_sremove :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (stree_t)))), (k @ (int (i32))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((s ∖ {[k]}) @ (stree_t))).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (alloc_initialized))
      → ∃ () : (), ((0) @ (int (i32))); True.
End spec.

Typeclasses Opaque tree_t_rec.
Typeclasses Opaque stree_t_rec.
