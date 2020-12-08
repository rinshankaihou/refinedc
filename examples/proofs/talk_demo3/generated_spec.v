From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo3 Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list Z) -d> typeO) → ((list Z) -d> typeO) := (λ self xs,
    ((xs <> []) @ (optional (&own (
      tyexists (λ y : Z,
      tyexists (λ ys : list Z,
      constrained (struct struct_list_node [@{type}
        (y @ (int (i32))) ;
        (guarded ("list_t_0") (apply_dfun self (ys)))
      ]) (
        ⌜xs = y :: ys⌝
      )))
    )) (null)))
  )%I.
  Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_ne : Contractive list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype := {|
    rty_type := (list Z);
    rty r__ := fixp list_t_rec r__
  |}.

  Lemma list_t_unfold (xs : list Z) :
    (xs @ list_t)%I ≡@{type} (
      ((xs <> []) @ (optional (&own (
        tyexists (λ y : Z,
        tyexists (λ ys : list Z,
        constrained (struct struct_list_node [@{type}
          (y @ (int (i32))) ;
          (guarded "list_t_0" (ys @ list_t))
        ]) (
          ⌜xs = y :: ys⌝
        )))
      )) (null)))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance list_t_rmovable : RMovable list_t :=
    {| rmovable 'xs := movable_eq _ _ (list_t_unfold xs) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance list_t_simplify_hyp_place_inst l_ β_ (xs : list Z) :
    SimplifyHypPlace l_ β_ (xs @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (list_t_unfold _)).
  Global Instance list_t_simplify_goal_place_inst l_ β_ (xs : list Z) :
    SimplifyGoalPlace l_ β_ (xs @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (list_t_unfold _)).

  Global Program Instance list_t_simplify_hyp_val_inst v_ (xs : list Z) :
    SimplifyHypVal v_ (xs @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (list_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance list_t_simplify_goal_val_inst v_ (xs : list Z) :
    SimplifyGoalVal v_ (xs @ list_t)%I (Some 100%N) :=
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
    fn(∀ (p, xs, ys) : loc * (list Z) * (list Z); (p @ (&own (xs @ (list_t)))), (ys @ (list_t)); True)
      → ∃ () : (), (void); (p ◁ₗ ((xs ++ ys) @ (list_t))).

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); (alloc_initialized)) → ∃ () : (), (void); True.
End spec.

Typeclasses Opaque list_t_rec.
