From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Definition of type [lock_test]. *)
  Definition lock_test_rec : (Z * Z * Z → type) → (Z * Z * Z → type) := (λ self patt__,
    let n1 := patt__.1.1 in
    let n2 := patt__.1.2 in
    let n3 := patt__.2 in
    ∃ₜ (l : lock_id),
    struct struct_lock_test [@{type}
      (n1 @ (int (size_t))) ;
      (spinlock (l)) ;
      (tylocked_ex (l) ("locked_int") (n2) (λ n,
        n @ (int (size_t))
      )) ;
      ((tylocked_ex (l) ("locked_struct") (n3) (λ n3,
        ∃ₜ (a : Z) (b : Z),
        constrained (struct struct_lock_test_inner [@{type}
          (a @ (int (size_t))) ;
          (b @ (int (size_t)))
        ]) (
          ⌜n3 = (a + b)%Z⌝ ∗
          ⌜n3 ∈ size_t⌝
        )
      )))
    ]
  )%I.
  Global Typeclasses Opaque lock_test_rec.

  Global Instance lock_test_rec_le : TypeMono lock_test_rec.
  Proof. solve_type_proper. Qed.

  Definition lock_test : rtype (Z * Z * Z) := {|
    rty r__ := lock_test_rec (type_fixpoint lock_test_rec) r__
  |}.

  Lemma lock_test_unfold (patt__ : Z * Z * Z):
    (patt__ @ lock_test)%I ≡@{type} (
      let n1 := patt__.1.1 in
      let n2 := patt__.1.2 in
      let n3 := patt__.2 in
      ∃ₜ (l : lock_id),
      struct struct_lock_test [@{type}
        (n1 @ (int (size_t))) ;
        (spinlock (l)) ;
        (tylocked_ex (l) ("locked_int") (n2) (λ n,
          n @ (int (size_t))
        )) ;
        ((tylocked_ex (l) ("locked_struct") (n3) (λ n3,
          ∃ₜ (a : Z) (b : Z),
          constrained (struct struct_lock_test_inner [@{type}
            (a @ (int (size_t))) ;
            (b @ (int (size_t)))
          ]) (
            ⌜n3 = (a + b)%Z⌝ ∗
            ⌜n3 ∈ size_t⌝
          )
        )))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 lock_test_rec). Qed.

  Definition lock_test_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (lock_test_unfold patt__) with 100%N].
  Global Existing Instance lock_test_simplify_hyp_place_inst_generated.
  Definition lock_test_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (lock_test_unfold patt__) with 100%N].
  Global Existing Instance lock_test_simplify_goal_place_inst_generated.

  Definition lock_test_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (lock_test_unfold patt__) with 100%N].
  Global Existing Instance lock_test_simplify_hyp_val_inst_generated.
  Definition lock_test_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (lock_test_unfold patt__) with 100%N].
  Global Existing Instance lock_test_simplify_goal_val_inst_generated.

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

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_lock_test)))); True)
      → ∃ () : (), (void); (p ◁ₗ ((0, 0, 10) @ (lock_test))).

  (* Specifications for function [write_outside]. *)
  Definition type_of_write_outside :=
    fn(∀ (p, n, n1, n2, n3) : loc * Z * Z * Z * Z; (p @ (&own ((n1, n2, n3) @ (lock_test)))), (n @ (int (size_t))); True)
      → ∃ () : (), (void); (p ◁ₗ ((n, n2, n3) @ (lock_test))).

  (* Specifications for function [read_outside]. *)
  Definition type_of_read_outside :=
    fn(∀ (p, n1, n2, n3) : loc * Z * Z * Z; (p @ (&own ((n1, n2, n3) @ (lock_test)))); True)
      → ∃ () : (), (n1 @ (int (size_t))); (p ◁ₗ ((n1, n2, n3) @ (lock_test))).

  (* Specifications for function [write_locked]. *)
  Definition type_of_write_locked :=
    fn(∀ (p, n, q, n1, n2, n3) : loc * Z * own_state * Z * Z * Z; (p @ (&frac{q} ((n1, n2, n3) @ (lock_test)))), (n @ (int (size_t))); True)
      → ∃ () : (), (void); (p ◁ₗ{q} ((n1, n, n3) @ (lock_test))).

  (* Specifications for function [read_locked]. *)
  Definition type_of_read_locked :=
    fn(∀ (p, q, n1, n2, n3) : loc * own_state * Z * Z * Z; (p @ (&frac{q} ((n1, n2, n3) @ (lock_test)))); True)
      → ∃ n : Z, (n @ (int (size_t))); (p ◁ₗ{q} ((n1, n2, n3) @ (lock_test))) ∗ ⌜q = Own → n = n2⌝.

  (* Specifications for function [increment]. *)
  Definition type_of_increment :=
    fn(∀ (p, q, n1, n2, n3) : loc * own_state * Z * Z * Z; (p @ (&frac{q} ((n1, n2, n3) @ (lock_test)))); True)
      → ∃ n : Z, (n @ (int (size_t))); (p ◁ₗ{q} ((n1, n2, n3) @ (lock_test))) ∗ ⌜q = Own → n ≤ n3⌝.
End spec.

Global Typeclasses Opaque lock_test_rec.
Global Typeclasses Opaque lock_test.
