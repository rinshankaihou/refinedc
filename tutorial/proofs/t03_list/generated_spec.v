From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition talloc_initialized := initialized "allocator_state" ().

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list type) → type) → ((list type) → type) := (λ self l,
    ((maybe2 cons l) @ (optionalO (λ patt__,
      let ty := patt__.1 in
      let l := patt__.2 in
      &own (
        struct struct_list [@{type}
          (&own (ty)) ;
          (self (l))
        ]
      )
    ) (null)))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype ((list type)) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (l : (list type)):
    (l @ list_t)%I ≡@{type} (
      ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (
          struct struct_list [@{type}
            (&own (ty)) ;
            (l @ list_t)
          ]
        )
      ) (null)))
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

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); (talloc_initialized)) → ∃ () : (), (void); True.

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ () : (); True) → ∃ () : (), (([]) @ (list_t)); True.

  (* Specifications for function [is_empty]. *)
  Definition type_of_is_empty :=
    fn(∀ (p, l) : loc * (list type); (p @ (&own (l @ (list_t)))); True)
      → ∃ () : (), ((bool_decide (l = [])) @ (builtin_boolean)); (p ◁ₗ (l @ (list_t))).

  (* Specifications for function [push]. *)
  Definition type_of_push :=
    fn(∀ (l, ty) : (list type) * type; (l @ (list_t)), (&own (ty)); (talloc_initialized))
      → ∃ () : (), ((ty :: l) @ (list_t)); True.

  (* Specifications for function [pop]. *)
  Definition type_of_pop :=
    fn(∀ (l, p) : (list type) * loc; (p @ (&own (l @ (list_t)))); (talloc_initialized))
      → ∃ () : (), ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (ty) ) null)); (p ◁ₗ ((tail l) @ (list_t))).

  (* Specifications for function [reverse]. *)
  Definition type_of_reverse :=
    fn(∀ l : (list type); (l @ (list_t)); True)
      → ∃ () : (), ((rev l) @ (list_t)); True.

  (* Specifications for function [length]. *)
  Definition type_of_length :=
    fn(∀ (p, l) : loc * (list type); (p @ (&own (l @ (list_t)))); ⌜length l ≤ max_int size_t⌝)
      → ∃ () : (), ((length l) @ (int (size_t))); (p ◁ₗ (l @ (list_t))).

  (* Specifications for function [length_val_rec]. *)
  Definition type_of_length_val_rec :=
    fn(∀ (v, l) : val * (list type); (at_value (v) (l @ (list_t))); ⌜length l ≤ max_int size_t⌝)
      → ∃ () : (), ((length l) @ (int (size_t))); (v ◁ᵥ (l @ (list_t))).

  (* Specifications for function [length_val]. *)
  Definition type_of_length_val :=
    fn(∀ (v, l) : val * (list type); (at_value (v) (l @ (list_t))); ⌜length l ≤ max_int size_t⌝)
      → ∃ () : (), ((length l) @ (int (size_t))); (v ◁ᵥ (l @ (list_t))).

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ (p, l1, l2) : loc * (list type) * (list type); (p @ (&own (l1 @ (list_t)))), (l2 @ (list_t)); True)
      → ∃ () : (), (void); (p ◁ₗ ((l1 ++ l2) @ (list_t))).

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (l, p, n) : (list Z) * loc * Z; (p @ (&own ((l `at_type` int size_t) @ (list_t)))), (n @ (int (size_t))); True)
      → ∃ b : bool, (b @ (builtin_boolean)); (p ◁ₗ ((l `at_type` int size_t) @ (list_t))) ∗ ⌜b ↔ n ∈ l⌝.

  (* Specifications for function [rev_append]. *)
  Definition type_of_rev_append :=
    fn(∀ (p, l1, l2) : loc * (list type) * (list type); (l1 @ (list_t)), (p @ (&own (l2 @ (list_t)))); True)
      → ∃ () : (), (void); (p ◁ₗ (((rev l1) ++ l2) @ (list_t))).
End spec.

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
