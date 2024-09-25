From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition ENTRY_LAYOUT := {| ly_size := 16%nat; ly_align_log := 3%nat |}.

  (* Definition of type [mpool_entry]. *)
  Definition mpool_entry_rec : (nat → type) → (nat → type) := (λ self n,
    padded (struct struct_mpool_entry [@{type}
      (((0 < n)%nat) @ (optional (&own (self (((n - 1)%nat)))) null))
    ]) struct_mpool_entry ENTRY_LAYOUT
  )%I.
  Global Typeclasses Opaque mpool_entry_rec.

  Global Instance mpool_entry_rec_le : TypeMono mpool_entry_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool_entry : rtype (nat) := {|
    rty r__ := mpool_entry_rec (type_fixpoint mpool_entry_rec) r__
  |}.

  Lemma mpool_entry_unfold (n : nat):
    (n @ mpool_entry)%I ≡@{type} (
      padded (struct struct_mpool_entry [@{type}
        (((0 < n)%nat) @ (optional (&own (((n - 1)%nat) @ mpool_entry)) null))
      ]) struct_mpool_entry ENTRY_LAYOUT
    )%I.
  Proof. apply: (type_fixpoint_unfold2 mpool_entry_rec). Qed.

  Definition mpool_entry_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (mpool_entry_unfold patt__) with 100%N].
  Global Existing Instance mpool_entry_simplify_hyp_place_inst_generated.
  Definition mpool_entry_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (mpool_entry_unfold patt__) with 100%N].
  Global Existing Instance mpool_entry_simplify_goal_place_inst_generated.

  Definition mpool_entry_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (mpool_entry_unfold patt__) with 100%N].
  Global Existing Instance mpool_entry_simplify_hyp_val_inst_generated.
  Definition mpool_entry_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (mpool_entry_unfold patt__) with 100%N].
  Global Existing Instance mpool_entry_simplify_goal_val_inst_generated.

  (* Definition of type [mpool]. *)
  Definition mpool_rec : (nat → type) → (nat → type) := (λ self n,
    struct struct_mpool [@{type}
      (((0 < n)%nat) @ (optional (&own (((n - 1)%nat) @ (mpool_entry))) null))
    ]
  )%I.
  Global Typeclasses Opaque mpool_rec.

  Global Instance mpool_rec_le : TypeMono mpool_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool : rtype (nat) := {|
    rty r__ := mpool_rec (type_fixpoint mpool_rec) r__
  |}.

  Lemma mpool_unfold (n : nat):
    (n @ mpool)%I ≡@{type} (
      struct struct_mpool [@{type}
        (((0 < n)%nat) @ (optional (&own (((n - 1)%nat) @ (mpool_entry))) null))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 mpool_rec). Qed.

  Definition mpool_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (mpool_unfold patt__) with 100%N].
  Global Existing Instance mpool_simplify_hyp_place_inst_generated.
  Definition mpool_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (mpool_unfold patt__) with 100%N].
  Global Existing Instance mpool_simplify_goal_place_inst_generated.

  Definition mpool_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (mpool_unfold patt__) with 100%N].
  Global Existing Instance mpool_simplify_hyp_val_inst_generated.
  Definition mpool_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (mpool_unfold patt__) with 100%N].
  Global Existing Instance mpool_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [mpool_init]. *)
  Definition type_of_mpool_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_mpool)))); True)
      → ∃ () : (), (void); (p ◁ₗ ((0%nat) @ (mpool))).

  (* Specifications for function [mpool_get]. *)
  Definition type_of_mpool_get :=
    fn(∀ (p, n) : loc * nat; (p @ (&own (n @ (mpool)))); True)
      → ∃ () : (), (((0 < n)%nat) @ (optional (&own (uninit (ENTRY_LAYOUT))) null)); (p ◁ₗ (((n - 1)%nat) @ (mpool))).

  (* Specifications for function [mpool_put]. *)
  Definition type_of_mpool_put :=
    fn(∀ (p, n) : loc * nat; (p @ (&own (n @ (mpool)))), (&own (uninit (ENTRY_LAYOUT))); True)
      → ∃ () : (), (void); (p ◁ₗ (((n + 1)%nat) @ (mpool))).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (global_with_type "e1" Own (uninit (ENTRY_LAYOUT))) ∗ (global_with_type "e2" Own (uninit (ENTRY_LAYOUT))))
      → ∃ () : (), (int (i32)); True.
End spec.

Global Typeclasses Opaque mpool_entry_rec.
Global Typeclasses Opaque mpool_entry.
Global Typeclasses Opaque mpool_rec.
Global Typeclasses Opaque mpool.
