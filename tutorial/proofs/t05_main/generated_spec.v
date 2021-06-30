From refinedc.typing Require Import typing.
From refinedc.tutorial.t05_main Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [latch]. *)
  Definition latch_rec : ((iProp Σ) -d> typeO) → ((iProp Σ) -d> typeO) := (λ self P,
    struct struct_latch [@{type}
      (atomic_bool (bool_it) ((□ P)) (True))
    ]
  )%I.
  Typeclasses Opaque latch_rec.

  Global Instance latch_rec_ne : Contractive latch_rec.
  Proof. solve_type_proper. Qed.

  Definition latch : rtype := {|
    rty_type := (iProp Σ);
    rty r__ := fixp latch_rec r__
  |}.

  Lemma latch_unfold (P : (iProp Σ)):
    (P @ latch)%I ≡@{type} (
      struct struct_latch [@{type}
        (atomic_bool (bool_it) ((□ P)) (True))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance latch_rmovable : RMovable latch :=
    {| rmovable patt__ := movable_eq _ _ (latch_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance latch_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (latch_unfold _)).
  Global Instance latch_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (latch_unfold _)).

  Global Program Instance latch_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (latch_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance latch_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (latch_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [alloc_entry_t]. *)
  Definition alloc_entry_t_rec : ((list nat) -d> typeO) → ((list nat) -d> typeO) := (λ self sizes,
    ((maybe2 cons sizes) @ (optionalO (λ patt__ : (nat * _),
      let size := patt__.1 in
      let l := patt__.2 in
      &own (
        constrained (padded (struct struct_alloc_entry [@{type}
          (size @ (int (size_t))) ;
          (guarded ("alloc_entry_t_0") (apply_dfun self (l)))
        ]) struct_alloc_entry (Layout size 3)) (
          ⌜(8 | size)⌝
        )
      )
    ) null))
  )%I.
  Typeclasses Opaque alloc_entry_t_rec.

  Global Instance alloc_entry_t_rec_ne : Contractive alloc_entry_t_rec.
  Proof. solve_type_proper. Qed.

  Definition alloc_entry_t : rtype := {|
    rty_type := (list nat);
    rty r__ := fixp alloc_entry_t_rec r__
  |}.

  Lemma alloc_entry_t_unfold (sizes : (list nat)):
    (sizes @ alloc_entry_t)%I ≡@{type} (
      ((maybe2 cons sizes) @ (optionalO (λ patt__ : (nat * _),
        let size := patt__.1 in
        let l := patt__.2 in
        &own (
          constrained (padded (struct struct_alloc_entry [@{type}
            (size @ (int (size_t))) ;
            (guarded "alloc_entry_t_0" (l @ alloc_entry_t))
          ]) struct_alloc_entry (Layout size 3)) (
            ⌜(8 | size)⌝
          )
        )
      ) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance alloc_entry_t_rmovable : RMovable alloc_entry_t :=
    {| rmovable patt__ := movable_eq _ _ (alloc_entry_t_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance alloc_entry_t_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ alloc_entry_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (alloc_entry_t_unfold _)).
  Global Instance alloc_entry_t_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ alloc_entry_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (alloc_entry_t_unfold _)).

  Global Program Instance alloc_entry_t_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ alloc_entry_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (alloc_entry_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance alloc_entry_t_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ alloc_entry_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (alloc_entry_t_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [alloc_state]. *)
  Definition alloc_state_rec : (() -d> typeO) → (() -d> typeO) := (λ self _,
    (
      tyexists (λ lid : lock_id,
      struct struct_alloc_state [@{type}
        (spinlock (lid)) ;
        (tylocked (lid) ("data") (alloc_entry_t))
      ])
    )
  )%I.
  Typeclasses Opaque alloc_state_rec.

  Global Instance alloc_state_rec_ne : Contractive alloc_state_rec.
  Proof. solve_type_proper. Qed.

  Definition alloc_state : rtype := {|
    rty_type := ();
    rty r__ := fixp alloc_state_rec r__
  |}.

  Lemma alloc_state_unfold (unit__ : ()):
    (unit__ @ alloc_state)%I ≡@{type} (
      (
        tyexists (λ lid : lock_id,
        struct struct_alloc_state [@{type}
          (spinlock (lid)) ;
          (tylocked (lid) ("data") (alloc_entry_t))
        ])
      )
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance alloc_state_rmovable : RMovable alloc_state :=
    {| rmovable patt__ := movable_eq _ _ (alloc_state_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance alloc_state_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ alloc_state)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (alloc_state_unfold _)).
  Global Instance alloc_state_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ alloc_state)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (alloc_state_unfold _)).

  Global Program Instance alloc_state_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ alloc_state)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (alloc_state_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance alloc_state_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ alloc_state)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (alloc_state_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [latch_wait]. *)
  Definition type_of_latch_wait :=
    fn(∀ (p, beta, P) : loc * own_state * (iProp Σ); (p @ (&frac{beta} (P @ (latch)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (P @ (latch))) ∗ (P).

  (* Specifications for function [latch_release]. *)
  Definition type_of_latch_release :=
    fn(∀ (p, beta, P) : loc * own_state * (iProp Σ); (p @ (&frac{beta} (P @ (latch)))); (□ P))
      → ∃ () : (), (void); (p ◁ₗ{beta} (P @ (latch))).

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); (alloc_initialized)) → ∃ () : (), (void); True.

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

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ size : nat; (size @ (int (size_t))); ⌜size + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (uninit (Layout size 3))); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ size : nat; (size @ (int (size_t))), (&own (uninit (Layout size 3))); (alloc_initialized) ∗ ⌜(8 | size)⌝)
      → ∃ () : (), (void); True.

  (* Specifications for function [alloc_array]. *)
  Definition type_of_alloc_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))); ⌜size * n + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); True.

  (* Specifications for function [free_array]. *)
  Definition type_of_free_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); ⌜size * n ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (void); True.

  (* Specifications for function [init_alloc]. *)
  Definition type_of_init_alloc :=
    fn(∀ () : (); (global_with_type "allocator_state" Own (uninit struct_alloc_state)))
      → ∃ () : (), (void); (alloc_initialized).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (initialized "initialized" ()) ∗ (global_with_type "allocator_state" Own (uninit (struct_alloc_state))) ∗ (global_with_type "allocator_data" Own (uninit (Layout (Z.to_nat 10000) 3))))
      → ∃ () : (), (int (i32)); True.

  (* Specifications for function [main2]. *)
  Definition type_of_main2 :=
    fn(∀ () : (); (initialized "initialized" ()))
      → ∃ () : (), (int (i32)); True.
End spec.

Typeclasses Opaque latch_rec.
Typeclasses Opaque alloc_entry_t_rec.
Typeclasses Opaque alloc_state_rec.
