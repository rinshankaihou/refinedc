From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t02_ownership Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t02_ownership.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition talloc_initialized := initialized "allocator_state" ().

  (* Definition of type [list_t]. *)
  Definition list_t_rec : (unit → type) → (unit → type) := (λ self x__,
    (optionalO (λ _ : unit,
      &own (
        struct struct_list_node [@{type}
          (int (i32)) ;
          (tyexists (λ rfmt__, self (rfmt__)))
        ]
      )
    ) (null))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype (unit) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (x__ : unit):
    (x__ @ list_t)%I ≡@{type} (
      (optionalO (λ _ : unit,
        &own (
          struct struct_list_node [@{type}
            (int (i32)) ;
            (tyexists (λ rfmt__, rfmt__ @ list_t))
          ]
        )
      ) (null))
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

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ () : (); (&own (list_t)), (list_t); True)
      → ∃ () : (), (void); True.

  (* Function [test] has been skipped. *)

  (* Specifications for function [append_2]. *)
  Definition type_of_append_2 :=
    fn(∀ p : loc; (p @ (&own (list_t))), (list_t); True)
      → ∃ () : (), (void); (p ◁ₗ (list_t)).

  (* Specifications for function [test_2]. *)
  Definition type_of_test_2 :=
    fn(∀ () : (); (talloc_initialized)) → ∃ () : (), (void); True.
End spec.

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
