From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo2 Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo2.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [list_t]. *)
  Definition list_t_rec : (unit -d> typeO) → (unit -d> typeO) := (λ self u,
    (optionalO (λ _ : unit,
      &own (
        struct struct_list_node [@{type}
          (int (i32)) ;
          (tyexists (λ rfmt__, guarded ("list_t_0") (apply_dfun self (rfmt__))))
        ]
      )
    ) (null))
  )%I.
  Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_ne : Contractive list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype := {|
    rty_type := unit;
    rty r__ := fixp list_t_rec r__
  |}.

  Lemma list_t_unfold (u : unit) :
    (u @ list_t)%I ≡@{type} (
      (optionalO (λ _ : unit,
        &own (
          struct struct_list_node [@{type}
            (int (i32)) ;
            (tyexists (λ rfmt__, guarded "list_t_0" (rfmt__ @ list_t)))
          ]
        )
      ) (null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance list_t_rmovable : RMovable list_t :=
    {| rmovable 'u := movable_eq _ _ (list_t_unfold u) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance list_t_simplify_hyp_place_inst l_ β_ (u : unit) :
    SimplifyHypPlace l_ β_ (u @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (list_t_unfold _)).
  Global Instance list_t_simplify_goal_place_inst l_ β_ (u : unit) :
    SimplifyGoalPlace l_ β_ (u @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (list_t_unfold _)).

  Global Program Instance list_t_simplify_hyp_val_inst v_ (u : unit) :
    SimplifyHypVal v_ (u @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (list_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance list_t_simplify_goal_val_inst v_ (u : unit) :
    SimplifyGoalVal v_ (u @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (list_t_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

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

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ () : (); (&own (list_t)), (list_t); True)
      → ∃ () : (), (void); True.

  (* Function [test] has been skipped. *)
End spec.

Typeclasses Opaque list_t_rec.
