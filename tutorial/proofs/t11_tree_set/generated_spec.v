From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition talloc_initialized := initialized "allocator_state" ().

  (* Definition of type [tree_t]. *)
  Definition tree_t_rec : ((gset Z) → type) → ((gset Z) → type) := (λ self s,
    ((s ≠ ∅) @ (optional (&own (
      ∃ₜ (sl : gset Z) (sr : gset Z) (k : Z),
      constrained (struct struct_tree [@{type}
        (self (sl)) ;
        (self (sr)) ;
        (k @ (int (size_t)))
      ]) (
        ⌜s = sl ∪ {[k]} ∪ sr⌝ ∗
        ⌜set_Forall (λ i, i < k) sl⌝ ∗
        ⌜set_Forall (λ i, k < i) sr⌝
      )
    )) null))
  )%I.
  Global Typeclasses Opaque tree_t_rec.

  Global Instance tree_t_rec_le : TypeMono tree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition tree_t : rtype ((gset Z)) := {|
    rty r__ := tree_t_rec (type_fixpoint tree_t_rec) r__
  |}.

  Lemma tree_t_unfold (s : (gset Z)):
    (s @ tree_t)%I ≡@{type} (
      ((s ≠ ∅) @ (optional (&own (
        ∃ₜ (sl : gset Z) (sr : gset Z) (k : Z),
        constrained (struct struct_tree [@{type}
          (sl @ tree_t) ;
          (sr @ tree_t) ;
          (k @ (int (size_t)))
        ]) (
          ⌜s = sl ∪ {[k]} ∪ sr⌝ ∗
          ⌜set_Forall (λ i, i < k) sl⌝ ∗
          ⌜set_Forall (λ i, k < i) sr⌝
        )
      )) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 tree_t_rec). Qed.

  Definition tree_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (tree_t_unfold patt__) with 100%N].
  Global Existing Instance tree_t_simplify_hyp_place_inst_generated.
  Definition tree_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (tree_t_unfold patt__) with 100%N].
  Global Existing Instance tree_t_simplify_goal_place_inst_generated.

  Definition tree_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (tree_t_unfold patt__) with 100%N].
  Global Existing Instance tree_t_simplify_hyp_val_inst_generated.
  Definition tree_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (tree_t_unfold patt__) with 100%N].
  Global Existing Instance tree_t_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [talloc]. *)
  Definition type_of_talloc :=
    fn(∀ size : nat; (size @ (int (size_t))); ⌜size + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (talloc_initialized))
      → ∃ () : (), (&own (uninit (Layout size 3))); True.

  (* Specifications for function [tfree]. *)
  Definition type_of_tfree :=
    fn(∀ size : nat; (size @ (int (size_t))), (&own (uninit (Layout size 3))); (talloc_initialized) ∗ ⌜(8 | size)⌝)
      → ∃ () : (), (void); True.

  (* Specifications for function [talloc_array]. *)
  Definition type_of_talloc_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))); ⌜size * n + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (talloc_initialized))
      → ∃ () : (), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); True.

  (* Specifications for function [tfree_array]. *)
  Definition type_of_tfree_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); ⌜size * n ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (talloc_initialized))
      → ∃ () : (), (void); True.

  (* Specifications for function [empty]. *)
  Definition type_of_empty :=
    fn(∀ () : (); True) → ∃ () : (), ((∅) @ (tree_t)); True.

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ k : Z; (k @ (int (size_t))); (talloc_initialized))
      → ∃ () : (), (({[k]}) @ (tree_t)); True.

  (* Specifications for function [node]. *)
  Definition type_of_node :=
    fn(∀ (sl, k, sr) : (gset Z) * Z * (gset Z); (sl @ (tree_t)), (k @ (int (size_t))), (sr @ (tree_t)); (talloc_initialized) ∗ ⌜set_Forall (λ i, i < k) sl⌝ ∗ ⌜set_Forall (λ i, k < i) sr⌝)
      → ∃ () : (), ((sl ∪ {[k]} ∪ sr) @ (tree_t)); True.

  (* Specifications for function [free_tree]. *)
  Definition type_of_free_tree :=
    fn(∀ p : loc; (p @ (&own (tree_t))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (uninit (void*))).

  (* Specifications for function [member_rec]. *)
  Definition type_of_member_rec :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); True)
      → ∃ () : (), ((bool_decide (k ∈ s)) @ (builtin_boolean)); (p ◁ₗ (s @ (tree_t))).

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); True)
      → ∃ () : (), ((bool_decide (k ∈ s)) @ (builtin_boolean)); (p ◁ₗ (s @ (tree_t))).

  (* Specifications for function [insert_rec]. *)
  Definition type_of_insert_rec :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (({[k]} ∪ s) @ (tree_t))).

  (* Specifications for function [insert]. *)
  Definition type_of_insert :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (({[k]} ∪ s) @ (tree_t))).

  (* Specifications for function [tree_max]. *)
  Definition type_of_tree_max :=
    fn(∀ (p, s) : loc * (gset Z); (p @ (&own (s @ (tree_t)))); ⌜s ≠ ∅⌝)
      → ∃ m : Z, (m @ (int (size_t))); ⌜m ∈ s⌝ ∗ ⌜set_Forall (λ i, i ≤ m) s⌝ ∗ (p ◁ₗ (s @ (tree_t))).

  (* Specifications for function [remove]. *)
  Definition type_of_remove :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (tree_t)))), (k @ (int (size_t))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((s ∖ {[k]}) @ (tree_t))).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (talloc_initialized))
      → ∃ () : (), ((0) @ (int (i32))); True.
End spec.

Global Typeclasses Opaque tree_t_rec.
Global Typeclasses Opaque tree_t.
