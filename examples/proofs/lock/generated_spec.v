From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Definition of type [lock_test]. *)
  Definition lock_test_rec : (Z * Z * Z -d> typeO) → (Z * Z * Z -d> typeO) := (λ self patt__,
    let n1 := patt__.1.1 in
    let n2 := patt__.1.2 in
    let n3 := patt__.2 in
    tyexists (λ l : lock_id,
    struct struct_lock_test [@{type}
      (n1 @ (int (size_t))) ;
      (spinlock (l)) ;
      (spinlocked_ex (l) ("locked_int") (n2) (λ n,
        n @ (int (size_t))
      )) ;
      ((spinlocked_ex (l) ("locked_struct") (n3) (λ n3,
        tyexists (λ a : Z,
        tyexists (λ b : Z,
        constrained (struct struct_lock_test_inner [@{type}
          (a @ (int (size_t))) ;
          (b @ (int (size_t)))
        ]) (
          ⌜n3 = (a + b)%Z⌝ ∗
          ⌜n3 ∈ size_t⌝
        )))
      )))
    ])
  )%I.
  Typeclasses Opaque lock_test_rec.

  Global Instance lock_test_rec_ne : Contractive lock_test_rec.
  Proof. solve_type_proper. Qed.

  Definition lock_test : rtype := {|
    rty_type := Z * Z * Z;
    rty r__ := fixp lock_test_rec r__
  |}.

  Lemma lock_test_unfold (patt__ : Z * Z * Z):
    (patt__ @ lock_test)%I ≡@{type} (
      let n1 := patt__.1.1 in
      let n2 := patt__.1.2 in
      let n3 := patt__.2 in
      tyexists (λ l : lock_id,
      struct struct_lock_test [@{type}
        (n1 @ (int (size_t))) ;
        (spinlock (l)) ;
        (spinlocked_ex (l) ("locked_int") (n2) (λ n,
          n @ (int (size_t))
        )) ;
        ((spinlocked_ex (l) ("locked_struct") (n3) (λ n3,
          tyexists (λ a : Z,
          tyexists (λ b : Z,
          constrained (struct struct_lock_test_inner [@{type}
            (a @ (int (size_t))) ;
            (b @ (int (size_t)))
          ]) (
            ⌜n3 = (a + b)%Z⌝ ∗
            ⌜n3 ∈ size_t⌝
          )))
        )))
      ])
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance lock_test_rmovable : RMovable lock_test :=
    {| rmovable patt__ := movable_eq _ _ (lock_test_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance lock_test_simplify_hyp_place_inst l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ lock_test)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (lock_test_unfold _)).
  Global Instance lock_test_simplify_goal_place_inst l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ lock_test)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (lock_test_unfold _)).

  Global Program Instance lock_test_simplify_hyp_val_inst v_ patt__:
    SimplifyHypVal v_ (patt__ @ lock_test)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (lock_test_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance lock_test_simplify_goal_val_inst v_ patt__:
    SimplifyGoalVal v_ (patt__ @ lock_test)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (lock_test_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [sl_init]. *)
  Definition type_of_sl_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_spinlock)))); True)
      → ∃ gamma : lock_id, (void); (p ◁ₗ (spinlock (gamma))).

  (* Specifications for function [sl_lock]. *)
  Definition type_of_sl_lock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (spinlock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (spinlock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

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

Typeclasses Opaque lock_test_rec.
