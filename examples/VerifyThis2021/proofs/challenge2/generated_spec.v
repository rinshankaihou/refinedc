From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.examples.VerifyThis2021.challenge2 Require Import defs.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge2.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [tree_t]. *)
  Definition tree_t_rec : ((tree Z) → type) → ((tree Z) → type) := (λ self t,
    ((node_data t) @ (optionalO (λ patt__,
      let l := patt__.1.1 in
      let k := patt__.1.2 in
      let r := patt__.2 in
      &own (
        struct struct_Node [@{type}
          (k @ (int (i32))) ;
          (self (l)) ;
          (self (r))
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
          struct struct_Node [@{type}
            (k @ (int (i32))) ;
            (l @ tree_t) ;
            (r @ tree_t)
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

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list Z) → type) → ((list Z) → type) := (λ self l,
    ((maybe2 cons l) @ (optionalO (λ patt__,
      let k := patt__.1 in
      let l := patt__.2 in
      &own (struct (struct_Node) [@{type} k @ (int (i32)) ; uninit (void*) ; self (l) ])
    ) null))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype ((list Z)) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (l : (list Z)):
    (l @ list_t)%I ≡@{type} (
      ((maybe2 cons l) @ (optionalO (λ patt__,
        let k := patt__.1 in
        let l := patt__.2 in
        &own (struct (struct_Node) [@{type} k @ (int (i32)) ; uninit (void*) ; l @ list_t ])
      ) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 list_t_rec). Qed.

  Definition list_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_place_inst_generated.
  Definition list_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_place_inst_generated.

  Definition list_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_val_inst_generated.
  Definition list_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [size_rec]. *)
  Definition type_of_size_rec :=
    fn(∀ (v, l) : val * (list Z); (at_value (v) (l @ (list_t))); ⌜length l ≤ max_int size_t⌝)
      → ∃ () : (), ((length l) @ (int (size_t))); (v ◁ᵥ (l @ (list_t))).

  (* Specifications for function [size_iter]. *)
  Definition type_of_size_iter :=
    fn(∀ (v, l) : val * (list Z); (at_value (v) (l @ (list_t))); ⌜length l ≤ max_int size_t⌝)
      → ∃ () : (), ((length l) @ (int (size_t))); (v ◁ᵥ (l @ (list_t))).

  (* Specifications for function [dll_to_bst_rec]. *)
  Definition type_of_dll_to_bst_rec :=
    fn(∀ (l, p, n) : (list Z) * loc * nat; (l @ (list_t)), (p @ (&own (uninit (void*)))), (n @ (int (size_t))); ⌜n ≤ length l⌝)
      → ∃ (t, l_rest) : (tree Z) * (list Z), (t @ (tree_t)); (p ◁ₗ (l_rest @ (list_t))) ∗ ⌜list_tree_eq_aux n l t l_rest⌝.

  (* Specifications for function [dll_to_bst]. *)
  Definition type_of_dll_to_bst :=
    fn(∀ l : (list Z); (l @ (list_t)); ⌜length l ≤ max_int size_t⌝)
      → ∃ t : (tree Z), (t @ (tree_t)); ⌜list_tree_eq l t⌝.
End spec.

Global Typeclasses Opaque tree_t_rec.
Global Typeclasses Opaque tree_t.
Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
