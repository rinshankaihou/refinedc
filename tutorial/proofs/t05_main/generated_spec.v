From refinedc.typing Require Import typing.
From refinedc.tutorial.t05_main Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Definition talloc_initialized := initialized "allocator_state" ().

  (* Definition of type [latch]. *)
  Definition latch_rec : ((iProp Σ) → type) → ((iProp Σ) → type) := (λ self P,
    struct struct_latch [@{type}
      (atomic_bool (u8) ((□ P)) (True))
    ]
  )%I.
  Global Typeclasses Opaque latch_rec.

  Global Instance latch_rec_le : TypeMono latch_rec.
  Proof. solve_type_proper. Qed.

  Definition latch : rtype ((iProp Σ)) := {|
    rty r__ := latch_rec (type_fixpoint latch_rec) r__
  |}.

  Lemma latch_unfold (P : (iProp Σ)):
    (P @ latch)%I ≡@{type} (
      struct struct_latch [@{type}
        (atomic_bool (u8) ((□ P)) (True))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 latch_rec). Qed.

  Definition latch_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_hyp_place_inst_generated.
  Definition latch_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_goal_place_inst_generated.

  Definition latch_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_hyp_val_inst_generated.
  Definition latch_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_goal_val_inst_generated.

  (* Definition of type [alloc_entry_t]. *)
  Definition alloc_entry_t_rec : ((list nat) → type) → ((list nat) → type) := (λ self sizes,
    ((maybe2 cons sizes) @ (optionalO (λ patt__ : (nat * _),
      let size := patt__.1 in
      let l := patt__.2 in
      &own (
        constrained (padded (struct struct_alloc_entry [@{type}
          (size @ (int (size_t))) ;
          (self (l))
        ]) struct_alloc_entry (Layout size 3)) (
          ⌜(8 | size)⌝
        )
      )
    ) null))
  )%I.
  Global Typeclasses Opaque alloc_entry_t_rec.

  Global Instance alloc_entry_t_rec_le : TypeMono alloc_entry_t_rec.
  Proof. solve_type_proper. Qed.

  Definition alloc_entry_t : rtype ((list nat)) := {|
    rty r__ := alloc_entry_t_rec (type_fixpoint alloc_entry_t_rec) r__
  |}.

  Lemma alloc_entry_t_unfold (sizes : (list nat)):
    (sizes @ alloc_entry_t)%I ≡@{type} (
      ((maybe2 cons sizes) @ (optionalO (λ patt__ : (nat * _),
        let size := patt__.1 in
        let l := patt__.2 in
        &own (
          constrained (padded (struct struct_alloc_entry [@{type}
            (size @ (int (size_t))) ;
            (l @ alloc_entry_t)
          ]) struct_alloc_entry (Layout size 3)) (
            ⌜(8 | size)⌝
          )
        )
      ) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 alloc_entry_t_rec). Qed.

  Definition alloc_entry_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (alloc_entry_t_unfold patt__) with 100%N].
  Global Existing Instance alloc_entry_t_simplify_hyp_place_inst_generated.
  Definition alloc_entry_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (alloc_entry_t_unfold patt__) with 100%N].
  Global Existing Instance alloc_entry_t_simplify_goal_place_inst_generated.

  Definition alloc_entry_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (alloc_entry_t_unfold patt__) with 100%N].
  Global Existing Instance alloc_entry_t_simplify_hyp_val_inst_generated.
  Definition alloc_entry_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (alloc_entry_t_unfold patt__) with 100%N].
  Global Existing Instance alloc_entry_t_simplify_goal_val_inst_generated.

  (* Definition of type [alloc_state]. *)
  Definition alloc_state_rec : (unit → type) → (unit → type) := (λ self x__,
    (
      ∃ₜ (lid : lock_id),
      struct struct_alloc_state [@{type}
        (spinlock (lid)) ;
        (tylocked (lid) ("data") (alloc_entry_t))
      ]
    )
  )%I.
  Global Typeclasses Opaque alloc_state_rec.

  Global Instance alloc_state_rec_le : TypeMono alloc_state_rec.
  Proof. solve_type_proper. Qed.

  Definition alloc_state : rtype (unit) := {|
    rty r__ := alloc_state_rec (type_fixpoint alloc_state_rec) r__
  |}.

  Lemma alloc_state_unfold (x__ : unit):
    (x__ @ alloc_state)%I ≡@{type} (
      (
        ∃ₜ (lid : lock_id),
        struct struct_alloc_state [@{type}
          (spinlock (lid)) ;
          (tylocked (lid) ("data") (alloc_entry_t))
        ]
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 alloc_state_rec). Qed.

  Definition alloc_state_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (alloc_state_unfold patt__) with 100%N].
  Global Existing Instance alloc_state_simplify_hyp_place_inst_generated.
  Definition alloc_state_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (alloc_state_unfold patt__) with 100%N].
  Global Existing Instance alloc_state_simplify_goal_place_inst_generated.

  Definition alloc_state_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (alloc_state_unfold patt__) with 100%N].
  Global Existing Instance alloc_state_simplify_hyp_val_inst_generated.
  Definition alloc_state_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (alloc_state_unfold patt__) with 100%N].
  Global Existing Instance alloc_state_simplify_goal_val_inst_generated.

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
    fn(∀ () : (); (talloc_initialized)) → ∃ () : (), (void); True.

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

  (* Specifications for function [init_talloc]. *)
  Definition type_of_init_talloc :=
    fn(∀ () : (); (global_with_type "allocator_state" Own (uninit struct_alloc_state)))
      → ∃ () : (), (void); (talloc_initialized).

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); (initialized "initialized" ()) ∗ (global_with_type "allocator_state" Own (uninit (struct_alloc_state))) ∗ (global_with_type "allocator_data" Own (uninit (Layout (Z.to_nat 10000) 3))))
      → ∃ () : (), (int (i32)); True.

  (* Specifications for function [main2]. *)
  Definition type_of_main2 :=
    fn(∀ () : (); (initialized "initialized" ()))
      → ∃ () : (), (int (i32)); True.
End spec.

Global Typeclasses Opaque latch_rec.
Global Typeclasses Opaque latch.
Global Typeclasses Opaque alloc_entry_t_rec.
Global Typeclasses Opaque alloc_entry_t.
Global Typeclasses Opaque alloc_state_rec.
Global Typeclasses Opaque alloc_state.
