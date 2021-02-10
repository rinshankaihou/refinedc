From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition ENTRY_LAYOUT := {| ly_size := 16%nat; ly_align_log := 3%nat |}.

  (* Definition of type [mpool_entry]. *)
  Definition mpool_entry_rec : (nat -d> typeO) → (nat -d> typeO) := (λ self n,
    padded (struct struct_mpool_entry [@{type}
      (((0 < n)%nat) @ (optional (&own (guarded ("mpool_entry_0") (apply_dfun self (((n - 1)%nat))))) null))
    ]) struct_mpool_entry ENTRY_LAYOUT
  )%I.
  Typeclasses Opaque mpool_entry_rec.

  Global Instance mpool_entry_rec_ne : Contractive mpool_entry_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool_entry : rtype := {|
    rty_type := nat;
    rty r__ := fixp mpool_entry_rec r__
  |}.

  Lemma mpool_entry_unfold (n : nat):
    (n @ mpool_entry)%I ≡@{type} (
      padded (struct struct_mpool_entry [@{type}
        (((0 < n)%nat) @ (optional (&own (guarded "mpool_entry_0" (((n - 1)%nat) @ mpool_entry))) null))
      ]) struct_mpool_entry ENTRY_LAYOUT
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mpool_entry_rmovable : RMovable mpool_entry :=
    {| rmovable patt__ := movable_eq _ _ (mpool_entry_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mpool_entry_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ mpool_entry)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mpool_entry_unfold _)).
  Global Instance mpool_entry_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ mpool_entry)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mpool_entry_unfold _)).

  Global Program Instance mpool_entry_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ mpool_entry)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mpool_entry_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mpool_entry_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ mpool_entry)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mpool_entry_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [mpool]. *)
  Definition mpool_rec : (nat -d> typeO) → (nat -d> typeO) := (λ self n,
    struct struct_mpool [@{type}
      (((0 < n)%nat) @ (optional (&own (((n - 1)%nat) @ (mpool_entry))) null))
    ]
  )%I.
  Typeclasses Opaque mpool_rec.

  Global Instance mpool_rec_ne : Contractive mpool_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool : rtype := {|
    rty_type := nat;
    rty r__ := fixp mpool_rec r__
  |}.

  Lemma mpool_unfold (n : nat):
    (n @ mpool)%I ≡@{type} (
      struct struct_mpool [@{type}
        (((0 < n)%nat) @ (optional (&own (((n - 1)%nat) @ (mpool_entry))) null))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mpool_rmovable : RMovable mpool :=
    {| rmovable patt__ := movable_eq _ _ (mpool_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mpool_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ mpool)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mpool_unfold _)).
  Global Instance mpool_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ mpool)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mpool_unfold _)).

  Global Program Instance mpool_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ mpool)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mpool_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mpool_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ mpool)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mpool_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

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
      → ∃ () : (), (void); True.
End spec.

Typeclasses Opaque mpool_entry_rec.
Typeclasses Opaque mpool_rec.
