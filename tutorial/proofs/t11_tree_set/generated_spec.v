From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [tree_t]. *)
  Definition tree_t_rec : ((gset Z) -d> typeO) → ((gset Z) -d> typeO) := (λ self s,
    ((s ≠ ∅) @ (optional (&own (
      tyexists (λ sl : gset Z,
      tyexists (λ sr : gset Z,
      tyexists (λ k : Z,
      constrained (struct struct_tree [@{type}
        (guarded ("tree_t_0") (apply_dfun self (sl))) ;
        (guarded ("tree_t_1") (apply_dfun self (sr))) ;
        (k @ (int (size_t)))
      ]) (
        ⌜s = sl ∪ {[k]} ∪ sr⌝ ∗
        ⌜∀ i, i ∈ sl → i < k⌝ ∗
        ⌜∀ i, i ∈ sr → k < i⌝
      ))))
    )) null))
  )%I.
  Typeclasses Opaque tree_t_rec.

  Global Instance tree_t_rec_ne : Contractive tree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition tree_t : rtype := {|
    rty_type := (gset Z);
    rty r__ := fixp tree_t_rec r__
  |}.

  Lemma tree_t_unfold (s : gset Z) :
    (s @ tree_t)%I ≡@{type} (
      ((s ≠ ∅) @ (optional (&own (
        tyexists (λ sl : gset Z,
        tyexists (λ sr : gset Z,
        tyexists (λ k : Z,
        constrained (struct struct_tree [@{type}
          (guarded "tree_t_0" (sl @ tree_t)) ;
          (guarded "tree_t_1" (sr @ tree_t)) ;
          (k @ (int (size_t)))
        ]) (
          ⌜s = sl ∪ {[k]} ∪ sr⌝ ∗
          ⌜∀ i, i ∈ sl → i < k⌝ ∗
          ⌜∀ i, i ∈ sr → k < i⌝
        ))))
      )) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance tree_t_rmovable : RMovable tree_t :=
    {| rmovable 's := movable_eq _ _ (tree_t_unfold s) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance tree_t_simplify_hyp_place_inst l_ β_ (s : gset Z) :
    SimplifyHypPlace l_ β_ (s @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (tree_t_unfold _)).
  Global Instance tree_t_simplify_goal_place_inst l_ β_ (s : gset Z) :
    SimplifyGoalPlace l_ β_ (s @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (tree_t_unfold _)).

  Global Program Instance tree_t_simplify_hyp_val_inst v_ (s : gset Z) :
    SimplifyHypVal v_ (s @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (tree_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance tree_t_simplify_goal_val_inst v_ (s : gset Z) :
    SimplifyGoalVal v_ (s @ tree_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (tree_t_unfold _) T _).
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
    fn(∀ () : (); True) → ∃ () : (), ((∅) @ (tree_t)); True.

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ k : Z; (k @ (int (size_t))); (alloc_initialized))
      → ∃ () : (), (({[k]}) @ (tree_t)); True.

  (* Specifications for function [node]. *)
  Definition type_of_node :=
    fn(∀ (sl, k, sr) : (gset Z) * Z * (gset Z); (sl @ (tree_t)), (k @ (int (size_t))), (sr @ (tree_t)); (alloc_initialized) ∗ ⌜∀ i, i ∈ sl → i < k⌝ ∗ ⌜∀ i, i ∈ sr → k < i⌝)
      → ∃ () : (), ((sl ∪ {[k]} ∪ sr) @ (tree_t)); True.

  (* Specifications for function [free_tree]. *)
  Definition type_of_free_tree :=
    fn(∀ p : loc; (p @ (&own (tree_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (uninit (void*))).

  (* Specifications for function [member_rec]. *)
  Definition type_of_member_rec :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); True)
      → ∃ () : (), ((bool_decide (k ∈ s)) @ (boolean (bool_it))); (p ◁ₗ (s @ (tree_t))).

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); True)
      → ∃ () : (), ((bool_decide (k ∈ s)) @ (boolean (bool_it))); (p ◁ₗ (s @ (tree_t))).

  (* Specifications for function [insert_rec]. *)
  Definition type_of_insert_rec :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (({[k]} ∪ s) @ (tree_t))).

  (* Specifications for function [insert]. *)
  Definition type_of_insert :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (({[k]} ∪ s) @ (tree_t))).

  (* Specifications for function [tree_max]. *)
  Definition type_of_tree_max :=
    fn(∀ (p, s) : loc * (gset Z); (p @ (&own (s @ (tree_t)))); ⌜s ≠ ∅⌝)
      → ∃ m : Z, (m @ (int (size_t))); ⌜m ∈ s⌝ ∗ ⌜∀ i, i ∈ s → i ≤ m⌝ ∗ (p ◁ₗ (s @ (tree_t))).

  (* Specifications for function [remove]. *)
  Definition type_of_remove :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((s ∖ {[k]}) @ (tree_t))).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (alloc_initialized))
      → ∃ () : (), ((0) @ (int (i32))); True.
End spec.

Typeclasses Opaque tree_t_rec.
