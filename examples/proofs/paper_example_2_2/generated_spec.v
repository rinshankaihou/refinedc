From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_2 Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_2.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Definition layout_of_nat : nat → layout := ly_set_size struct_chunk.
  Coercion layout_of_nat : nat >-> layout.

  Close Scope Z.

  (* Definition of type [chunks_t]. *)
  Definition chunks_t_rec : ((gmultiset nat) → type) → ((gmultiset nat) → type) := (λ self s,
    ((s ≠ ∅) @ (optional (&own (
      ∃ₜ (n : nat) (tail : gmultiset nat),
      constrained (padded (struct struct_chunk [@{type}
        (n @ (int (size_t))) ;
        (self (tail))
      ]) struct_chunk n) (
        ⌜s = {[+n+]} ⊎ tail⌝ ∗
        ⌜∀ k, k ∈ tail → n ≤ k⌝
      )
    )) (null)))
  )%I.
  Global Typeclasses Opaque chunks_t_rec.

  Global Instance chunks_t_rec_le : TypeMono chunks_t_rec.
  Proof. solve_type_proper. Qed.

  Definition chunks_t : rtype ((gmultiset nat)) := {|
    rty r__ := chunks_t_rec (type_fixpoint chunks_t_rec) r__
  |}.

  Lemma chunks_t_unfold (s : (gmultiset nat)):
    (s @ chunks_t)%I ≡@{type} (
      ((s ≠ ∅) @ (optional (&own (
        ∃ₜ (n : nat) (tail : gmultiset nat),
        constrained (padded (struct struct_chunk [@{type}
          (n @ (int (size_t))) ;
          (tail @ chunks_t)
        ]) struct_chunk n) (
          ⌜s = {[+n+]} ⊎ tail⌝ ∗
          ⌜∀ k, k ∈ tail → n ≤ k⌝
        )
      )) (null)))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 chunks_t_rec). Qed.

  Definition chunks_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (chunks_t_unfold patt__) with 100%N].
  Global Existing Instance chunks_t_simplify_hyp_place_inst_generated.
  Definition chunks_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (chunks_t_unfold patt__) with 100%N].
  Global Existing Instance chunks_t_simplify_goal_place_inst_generated.

  Definition chunks_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (chunks_t_unfold patt__) with 100%N].
  Global Existing Instance chunks_t_simplify_hyp_val_inst_generated.
  Definition chunks_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (chunks_t_unfold patt__) with 100%N].
  Global Existing Instance chunks_t_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [sl_init]. *)
  Definition type_of_sl_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_spinlock)))); True)
      → ∃ gamma : lock_id, (void); (p ◁ₗ (spinlock (gamma))).

  (* Specifications for function [sl_lock]. *)
  Definition type_of_sl_lock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (lock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (lock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

  (* Specifications for function [sl_lock_both]. *)
  Definition type_of_sl_lock_both :=
    fn(∀ (p2, gamma2, beta2, p1, gamma1, beta1) : loc * lock_id * own_state * loc * lock_id * own_state; (p2 @ (&frac{beta2} (spinlock (gamma2)))), (p1 @ (&frac{beta1} (spinlock (gamma1)))); True)
      → ∃ () : (), (void); (p2 ◁ₗ{beta2} (spinlock (gamma2))) ∗ (lock_token gamma2 []) ∗ (p1 ◁ₗ{beta1} (spinlock (gamma1))) ∗ (lock_token gamma1 []).

  (* Specifications for function [sl_lock_both_same_prov]. *)
  Definition type_of_sl_lock_both_same_prov :=
    fn(∀ (p2, gamma2, beta2, p1, gamma1, beta1) : loc * lock_id * own_state * loc * lock_id * own_state; (p2 @ (&frac{beta2} (spinlock (gamma2)))), (p1 @ (&frac{beta1} (spinlock (gamma1)))); ⌜p1.1 = p2.1⌝)
      → ∃ () : (), (void); (p2 ◁ₗ{beta2} (spinlock (gamma2))) ∗ (lock_token gamma2 []) ∗ (p1 ◁ₗ{beta1} (spinlock (gamma1))) ∗ (lock_token gamma1 []).

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ (s, p, n) : (gmultiset nat) * loc * nat; (p @ (&own (s @ (chunks_t)))), (&own (uninit (n))), (n @ (int (size_t))); ⌜sizeof(struct_chunk) ≤ n⌝)
      → ∃ () : (), (void); (p ◁ₗ (({[+n+]} ⊎ s) @ (chunks_t))).
End spec.

Global Typeclasses Opaque chunks_t_rec.
Global Typeclasses Opaque chunks_t.
