From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo_alloc Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Notation "P ? l : r" :=
    (if bool_decide P then l else r)
    (at level 100, l at next level, r at next level).

  Close Scope Z.

  (*Definition byte_layout : nat → layout := ly_set_size u8.*)
  Definition byte_layout : nat → layout := mk_array_layout u8.
  Coercion byte_layout : nat >-> layout.

  Notation Uninit := (∃ₜ n : nat, uninit n)%I.

  (* Definition of type [mem_t]. *)
  Definition mem_t_rec : (nat → type) → (nat → type) := (λ self a,
    struct struct_mem_t [@{type}
      (a @ (int (size_t))) ;
      (&own (uninit (a)))
    ]
  )%I.
  Global Typeclasses Opaque mem_t_rec.

  Global Instance mem_t_rec_le : TypeMono mem_t_rec.
  Proof. solve_type_proper. Qed.

  Definition mem_t : rtype (nat) := {|
    rty r__ := mem_t_rec (type_fixpoint mem_t_rec) r__
  |}.

  Lemma mem_t_unfold (a : nat):
    (a @ mem_t)%I ≡@{type} (
      struct struct_mem_t [@{type}
        (a @ (int (size_t))) ;
        (&own (uninit (a)))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 mem_t_rec). Qed.

  Definition mem_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (mem_t_unfold patt__) with 100%N].
  Global Existing Instance mem_t_simplify_hyp_place_inst_generated.
  Definition mem_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (mem_t_unfold patt__) with 100%N].
  Global Existing Instance mem_t_simplify_goal_place_inst_generated.

  Definition mem_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (mem_t_unfold patt__) with 100%N].
  Global Existing Instance mem_t_simplify_hyp_val_inst_generated.
  Definition mem_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (mem_t_unfold patt__) with 100%N].
  Global Existing Instance mem_t_simplify_goal_val_inst_generated.

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

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ (p, a, n) : loc * nat * nat; (p @ (&own (a @ (mem_t)))), (n @ (int (size_t))); ⌜n <= a⌝)
      → ∃ () : (), (&own (uninit (n))); (p ◁ₗ ((a - n) @ (mem_t))).

  (* Specifications for function [client]. *)
  Definition type_of_client :=
    fn(∀ () : (); (&own ((10) @ (mem_t))); True)
      → ∃ () : (), ((2) @ (int (u8))); True.
End spec.

Global Typeclasses Opaque mem_t_rec.
Global Typeclasses Opaque mem_t.
