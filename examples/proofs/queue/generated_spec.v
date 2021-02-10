From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [queue_elem]. *)
  Definition queue_elem_rec : (type * type -d> typeO) → (type * type -d> typeO) := (λ self patt__,
    let ty := patt__.1 in
    let cont := patt__.2 in
    (&own (
      struct struct_queue_elem [@{type}
        (&own (ty)) ;
        (cont)
      ]
    ))
  )%I.
  Typeclasses Opaque queue_elem_rec.

  Global Instance queue_elem_rec_ne : Contractive queue_elem_rec.
  Proof. solve_type_proper. Qed.

  Definition queue_elem (cont : type) : rtype := {|
    rty_type := type;
    rty r__ := fixp queue_elem_rec (r__, cont)
  |}.

  Lemma queue_elem_unfold (cont : type) (ty : type):
    (ty @ queue_elem cont)%I ≡@{type} (
      (&own (
        struct struct_queue_elem [@{type}
          (&own (ty)) ;
          (cont)
        ]
      ))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance queue_elem_rmovable (cont : type) : RMovable (queue_elem cont) :=
    {| rmovable patt__ := movable_eq _ _ (queue_elem_unfold cont patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance queue_elem_simplify_hyp_place_inst_generated l_ β_ (cont : type) patt__:
    SimplifyHypPlace l_ β_ (patt__ @ queue_elem cont)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (queue_elem_unfold _ _)).
  Global Instance queue_elem_simplify_goal_place_inst_generated l_ β_ (cont : type) patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ queue_elem cont)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (queue_elem_unfold _ _)).

  Global Program Instance queue_elem_simplify_hyp_val_inst_generated v_ (cont : type) patt__:
    SimplifyHypVal v_ (patt__ @ queue_elem cont)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (queue_elem_unfold _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance queue_elem_simplify_goal_val_inst_generated v_ (cont : type) patt__:
    SimplifyGoalVal v_ (patt__ @ queue_elem cont)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (queue_elem_unfold _ _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [queue]. *)
  Definition queue_rec : ((list type) -d> typeO) → ((list type) -d> typeO) := (λ self tys,
    (&own (
      tyexists (λ p : loc,
      struct struct_queue [@{type}
        (tyfold ((λ ty x, ty @ queue_elem x) <$> tys) (place (p))) ;
        (p @ (&own (null)))
      ])
    ))
  )%I.
  Typeclasses Opaque queue_rec.

  Global Instance queue_rec_ne : Contractive queue_rec.
  Proof. solve_type_proper. Qed.

  Definition queue : rtype := {|
    rty_type := (list type);
    rty r__ := fixp queue_rec r__
  |}.

  Lemma queue_unfold (tys : (list type)):
    (tys @ queue)%I ≡@{type} (
      (&own (
        tyexists (λ p : loc,
        struct struct_queue [@{type}
          (tyfold ((λ ty x, ty @ queue_elem x) <$> tys) (place (p))) ;
          (p @ (&own (null)))
        ])
      ))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance queue_rmovable : RMovable queue :=
    {| rmovable patt__ := movable_eq _ _ (queue_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance queue_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ queue)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (queue_unfold _)).
  Global Instance queue_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ queue)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (queue_unfold _)).

  Global Program Instance queue_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ queue)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (queue_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance queue_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ queue)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (queue_unfold _) T _).
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

  (* Specifications for function [init_queue]. *)
  Definition type_of_init_queue :=
    fn(∀ () : (); (alloc_initialized))
      → ∃ () : (), (([]) @ (queue)); True.

  (* Specifications for function [is_empty]. *)
  Definition type_of_is_empty :=
    fn(∀ (p, tys) : loc * (list type); (p @ (&own ((tys) @ (queue)))); True)
      → ∃ () : (), ((bool_decide (tys ≠ [])) @ (boolean (bool_it))); (p ◁ₗ ((tys) @ (queue))).

  (* Specifications for function [enqueue]. *)
  Definition type_of_enqueue :=
    fn(∀ (p, tys, ty) : loc * (list type) * type; (p @ (&own ((tys) @ (queue)))), (&own (ty)); (alloc_initialized))
      → ∃ () : (), (void); (p ◁ₗ ((tys ++ [ty]) @ (queue))).

  (* Specifications for function [dequeue]. *)
  Definition type_of_dequeue :=
    fn(∀ (p, tys) : loc * (list type); (p @ (&own ((tys) @ (queue)))); (alloc_initialized))
      → ∃ () : (), ((maybe2 cons tys) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let _ := patt__.2 in
        &own (ty) ) null)); (p ◁ₗ ((tail tys) @ (queue))).
End spec.

Notation "queue_elem< cont >" := (queue_elem cont)
  (only printing, format "'queue_elem<' cont '>'") : printing_sugar.

Typeclasses Opaque queue_elem_rec.
Typeclasses Opaque queue_rec.
