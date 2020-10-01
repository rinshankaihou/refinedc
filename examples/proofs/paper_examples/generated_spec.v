From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Definition of type [alloc_data]. *)
  Definition alloc_data_rec : (nat -d> typeO) → (nat -d> typeO) := (λ self nlen,
    struct struct_alloc_data [@{type}
      (nlen @ (int (size_t))) ;
      (&own (uninit (ly_set_size u8 nlen)))
    ]
  )%I.
  Typeclasses Opaque alloc_data_rec.

  Global Instance alloc_data_rec_ne : Contractive alloc_data_rec.
  Proof. solve_type_proper. Qed.

  Definition alloc_data : rtype := {|
    rty_type := nat;
    rty r__ := fixp alloc_data_rec r__
  |}.

  Lemma alloc_data_unfold (nlen : nat) :
    (nlen @ alloc_data)%I ≡@{type} (
      struct struct_alloc_data [@{type}
        (nlen @ (int (size_t))) ;
        (&own (uninit (ly_set_size u8 nlen)))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance alloc_data_rmovable : RMovable alloc_data :=
    {| rmovable 'nlen := movable_eq _ _ (alloc_data_unfold nlen) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance alloc_data_simplify_hyp_place_inst l_ β_ (nlen : nat) :
    SimplifyHypPlace l_ β_ (nlen @ alloc_data)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (alloc_data_unfold _)).
  Global Instance alloc_data_simplify_goal_place_inst l_ β_ (nlen : nat) :
    SimplifyGoalPlace l_ β_ (nlen @ alloc_data)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (alloc_data_unfold _)).

  Global Program Instance alloc_data_simplify_hyp_val_inst v_ (nlen : nat) :
    SimplifyHypVal v_ (nlen @ alloc_data)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (alloc_data_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance alloc_data_simplify_goal_val_inst v_ (nlen : nat) :
    SimplifyGoalVal v_ (nlen @ alloc_data)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (alloc_data_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [chunks_t]. *)
  Definition chunks_t_rec : ((gmultiset layout) -d> typeO) → ((gmultiset layout) -d> typeO) := (λ self s,
    ((s ≠ ∅) @ (optional (&own (
      tyexists (λ ly : layout,
      tyexists (λ tail : gmultiset layout,
      constrained (padded (struct struct_chunk [@{type}
        ((ly.(ly_size)) @ (int (size_t))) ;
        (guarded ("chunks_t_0") (apply_dfun self (tail)))
      ]) struct_chunk ly) (
        ⌜s = {[ly]} ⊎ tail⌝ ∗
        ⌜∀ k, k ∈ tail → ly.(ly_size) ≤ k.(ly_size)⌝
      )))
    )) (null)))
  )%I.
  Typeclasses Opaque chunks_t_rec.

  Global Instance chunks_t_rec_ne : Contractive chunks_t_rec.
  Proof. solve_type_proper. Qed.

  Definition chunks_t : rtype := {|
    rty_type := (gmultiset layout);
    rty r__ := fixp chunks_t_rec r__
  |}.

  Lemma chunks_t_unfold (s : gmultiset layout) :
    (s @ chunks_t)%I ≡@{type} (
      ((s ≠ ∅) @ (optional (&own (
        tyexists (λ ly : layout,
        tyexists (λ tail : gmultiset layout,
        constrained (padded (struct struct_chunk [@{type}
          ((ly.(ly_size)) @ (int (size_t))) ;
          (guarded "chunks_t_0" (tail @ chunks_t))
        ]) struct_chunk ly) (
          ⌜s = {[ly]} ⊎ tail⌝ ∗
          ⌜∀ k, k ∈ tail → ly.(ly_size) ≤ k.(ly_size)⌝
        )))
      )) (null)))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance chunks_t_rmovable : RMovable chunks_t :=
    {| rmovable 's := movable_eq _ _ (chunks_t_unfold s) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance chunks_t_simplify_hyp_place_inst l_ β_ (s : gmultiset layout) :
    SimplifyHypPlace l_ β_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (chunks_t_unfold _)).
  Global Instance chunks_t_simplify_goal_place_inst l_ β_ (s : gmultiset layout) :
    SimplifyGoalPlace l_ β_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (chunks_t_unfold _)).

  Global Program Instance chunks_t_simplify_hyp_val_inst v_ (s : gmultiset layout) :
    SimplifyHypVal v_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (chunks_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance chunks_t_simplify_goal_val_inst v_ (s : gmultiset layout) :
    SimplifyGoalVal v_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (chunks_t_unfold _) T _).
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

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ (nlen, nsize, p) : nat * nat * loc; (p @ (&own (nlen @ (alloc_data)))), (nsize @ (int (size_t))); True)
      → ∃ () : (), ((nsize <= nlen) @ (optional (&own (uninit (ly_set_size u8 nsize))) (null))); (p ◁ₗ ((if bool_decide(nsize <= nlen) then (nlen - nsize)%nat else nlen) @ (alloc_data))).

  (* Specifications for function [thread_safe_alloc]. *)
  Definition type_of_thread_safe_alloc :=
    fn(∀ (lid, nsize) : lock_id * nat; (nsize @ (int (size_t))); (initialized "lock" lid) ∗ (initialized "data" lid))
      → ∃ () : (), (optionalO (λ _ : unit,
        &own (uninit (ly_set_size u8 nsize)) ) (null)); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ (s, p, ly) : (gmultiset layout) * loc * layout; (p @ (&own (s @ (chunks_t)))), (&own (uninit (ly))), ((ly.(ly_size)) @ (int (size_t))); ⌜layout_of struct_chunk ⊑ ly⌝)
      → ∃ () : (), (void); (p ◁ₗ (({[ly]} ⊎ s) @ (chunks_t))).

  (* Specifications for function [fork]. *)
  Definition type_of_fork :=
    fn(∀ (ty, P) : type * (iProp Σ); (function_ptr (fn(∀ () : (); &own ty; P) → ∃ () : (), void; True)), (&own (ty)); (P))
      → ∃ () : (), (void); True.

  (* Specifications for function [test_thread_safe_alloc_fork_fn]. *)
  Definition type_of_test_thread_safe_alloc_fork_fn :=
    fn(∀ () : (); (&own (tyexists (λ n : nat, n @ (int (size_t))))); (∃ lid : gname, initialized "lock" lid ∗ initialized "data" lid))
      → ∃ () : (), (void); True.

  (* Specifications for function [test_thread_safe_alloc]. *)
  Definition type_of_test_thread_safe_alloc :=
    fn(∀ lid : gname; (initialized "lock" lid) ∗ (initialized "data" lid) ∗ (global_with_type "param" Own (uninit size_t)))
      → ∃ () : (), (void); True.
End spec.

Typeclasses Opaque alloc_data_rec.
Typeclasses Opaque chunks_t_rec.
