From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition talloc_initialized := initialized "allocator_state" ().

  (* Definition of type [tree_t]. *)
  Definition tree_t_rec : ((tree Z) → type) → ((tree Z) → type) := (λ self t,
    ((node_data t) @ (optionalO (λ patt__,
      let l := patt__.1.1 in
      let k := patt__.1.2 in
      let r := patt__.2 in
      &own (
        struct struct_tree [@{type}
          (self (l)) ;
          (self (r)) ;
          (k @ (int (i32)))
        ]
      )
    ) null))
  )%I.
  Global Typeclasses Opaque tree_t_rec.

  Global Instance tree_t_rec_le : TypeMono tree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition tree_t : rtype ((tree Z)) := {|
    rty r__ := tree_t_rec (type_fixpoint tree_t_rec) r__
  |}.

  Lemma tree_t_unfold (t : (tree Z)):
    (t @ tree_t)%I ≡@{type} (
      ((node_data t) @ (optionalO (λ patt__,
        let l := patt__.1.1 in
        let k := patt__.1.2 in
        let r := patt__.2 in
        &own (
          struct struct_tree [@{type}
            (l @ tree_t) ;
            (r @ tree_t) ;
            (k @ (int (i32)))
          ]
        )
      ) null))
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

  (* Definition of type [stree_t]. *)
  Definition stree_t_rec : ((gset Z) → type) → ((gset Z) → type) := (λ self s,
    (∃ₜ t, constrained (t @ (tree_t)) ⌜tree_rel s t⌝)
  )%I.
  Global Typeclasses Opaque stree_t_rec.

  Global Instance stree_t_rec_le : TypeMono stree_t_rec.
  Proof. solve_type_proper. Qed.

  Definition stree_t : rtype ((gset Z)) := {|
    rty r__ := stree_t_rec (type_fixpoint stree_t_rec) r__
  |}.

  Lemma stree_t_unfold (s : (gset Z)):
    (s @ stree_t)%I ≡@{type} (
      (∃ₜ t, constrained (t @ (tree_t)) ⌜tree_rel s t⌝)
    )%I.
  Proof. apply: (type_fixpoint_unfold2 stree_t_rec). Qed.

  Definition stree_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (stree_t_unfold patt__) with 90%N].
  Global Existing Instance stree_t_simplify_hyp_place_inst_generated.
  Definition stree_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (stree_t_unfold patt__) with 90%N].
  Global Existing Instance stree_t_simplify_goal_place_inst_generated.

  Definition stree_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (stree_t_unfold patt__) with 90%N].
  Global Existing Instance stree_t_simplify_hyp_val_inst_generated.
  Definition stree_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (stree_t_unfold patt__) with 90%N].
  Global Existing Instance stree_t_simplify_goal_val_inst_generated.

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
    fn(∀ () : (); True) → ∃ () : (), (leaf @ (tree_t)); True.

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ k : Z; (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), ((node leaf k leaf) @ (tree_t)); True.

  (* Specifications for function [node]. *)
  Definition type_of_node :=
    fn(∀ (l, k, r) : (tree Z) * Z * (tree Z); (l @ (tree_t)), (k @ (int (i32))), (r @ (tree_t)); (talloc_initialized))
      → ∃ () : (), ((node l k r) @ (tree_t)); True.

  (* Specifications for function [free_tree]. *)
  Definition type_of_free_tree :=
    fn(∀ p : loc; (p @ (&own (tree_t))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (uninit (void*))).

  (* Specifications for function [member_rec]. *)
  Definition type_of_member_rec :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); True)
      → ∃ b : bool, (b @ (builtin_boolean)); (p ◁ₗ (t @ (tree_t))) ∗ ⌜b ↔ tree_member k t⌝.

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); True)
      → ∃ b : bool, (b @ (builtin_boolean)); (p ◁ₗ (t @ (tree_t))) ∗ ⌜b ↔ tree_member k t⌝.

  (* Specifications for function [insert_rec]. *)
  Definition type_of_insert_rec :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tree_insert k t) @ (tree_t))).

  (* Specifications for function [insert]. *)
  Definition type_of_insert :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tree_insert k t) @ (tree_t))).

  (* Specifications for function [tree_max]. *)
  Definition type_of_tree_max :=
    fn(∀ (p, l, k, r) : loc * (tree Z) * Z * (tree Z); (p @ (&own ((node l k r) @ (tree_t)))); True)
      → ∃ res : Z, (res @ (int (i32))); ⌜tree_max (node l k r) = Some res⌝ ∗ (p ◁ₗ ((node l k r) @ (tree_t))).

  (* Specifications for function [remove]. *)
  Definition type_of_remove :=
    fn(∀ (p, t, k) : loc * (tree Z) * Z; (p @ (&own (t @ (tree_t)))), (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tree_remove k t) @ (tree_t))).

  (* Specifications for function [sempty]. *)
  Definition type_of_sempty :=
    fn(∀ () : (); True) → ∃ () : (), ((∅) @ (stree_t)); True.

  (* Specifications for function [sinit]. *)
  Definition type_of_sinit :=
    fn(∀ k : Z; (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), (({[k]}) @ (stree_t)); True.

  (* Specifications for function [sfree_tree]. *)
  Definition type_of_sfree_tree :=
    fn(∀ p : loc; (p @ (&own (stree_t))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (uninit (void*))).

  (* Specifications for function [smember]. *)
  Definition type_of_smember :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (stree_t)))), (k @ (int (i32))); True)
      → ∃ b : bool, (b @ (builtin_boolean)); (p ◁ₗ (s @ (stree_t))) ∗ ⌜b ↔ k ∈ s⌝.

  (* Specifications for function [sinsert]. *)
  Definition type_of_sinsert :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (stree_t)))), (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ (({[k]} ∪ s) @ (stree_t))).

  (* Specifications for function [sremove]. *)
  Definition type_of_sremove :=
    fn(∀ (p, s, k) : loc * (gset Z) * Z; (p @ (&own (s @ (stree_t)))), (k @ (int (i32))); (talloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((s ∖ {[k]}) @ (stree_t))).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (talloc_initialized))
      → ∃ () : (), ((0) @ (int (i32))); True.
End spec.

Global Typeclasses Opaque tree_t_rec.
Global Typeclasses Opaque tree_t.
Global Typeclasses Opaque stree_t_rec.
Global Typeclasses Opaque stree_t.
