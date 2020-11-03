From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list type) -d> typeO) → ((list type) -d> typeO) := (λ self l,
    ((maybe2 cons l) @ (optionalO (λ patt__,
      let ty := patt__.1 in
      let l := patt__.2 in
      &own (
        struct struct_list [@{type}
          (&own (ty)) ;
          (guarded ("list_t_0") (apply_dfun self (l)))
        ]
      )
    ) null))
  )%I.
  Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_ne : Contractive list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype := {|
    rty_type := (list type);
    rty r__ := fixp list_t_rec r__
  |}.

  Lemma list_t_unfold (l : list type) :
    (l @ list_t)%I ≡@{type} (
      ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (
          struct struct_list [@{type}
            (&own (ty)) ;
            (guarded "list_t_0" (l @ list_t))
          ]
        )
      ) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance list_t_rmovable : RMovable list_t :=
    {| rmovable 'l := movable_eq _ _ (list_t_unfold l) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance list_t_simplify_hyp_place_inst l_ β_ (l : list type) :
    SimplifyHypPlace l_ β_ (l @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (list_t_unfold _)).
  Global Instance list_t_simplify_goal_place_inst l_ β_ (l : list type) :
    SimplifyGoalPlace l_ β_ (l @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (list_t_unfold _)).

  Global Program Instance list_t_simplify_hyp_val_inst v_ (l : list type) :
    SimplifyHypVal v_ (l @ list_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (list_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance list_t_simplify_goal_val_inst v_ (l : list type) :
    SimplifyGoalVal v_ (l @ list_t)%I (Some 100%N) :=
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

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); (alloc_initialized)) → ∃ () : (), (void); True.

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ () : (); True) → ∃ () : (), (([]) @ (list_t)); True.

  (* Specifications for function [is_empty]. *)
  Definition type_of_is_empty :=
    fn(∀ (p, l) : loc * (list type); (p @ (&own (l @ (list_t)))); True)
      → ∃ () : (), ((bool_decide (l = [])) @ (boolean (bool_it))); (p ◁ₗ (l @ (list_t))).

  (* Specifications for function [push]. *)
  Definition type_of_push :=
    fn(∀ (l, ty) : (list type) * type; (l @ (list_t)), (&own (ty)); (alloc_initialized))
      → ∃ () : (), ((ty :: l) @ (list_t)); True.

  (* Specifications for function [pop]. *)
  Definition type_of_pop :=
    fn(∀ (l, p) : (list type) * loc; (p @ (&own (l @ (list_t)))); (alloc_initialized))
      → ∃ () : (), ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (ty) ) null)); (p ◁ₗ ((tail l) @ (list_t))).

  (* Specifications for function [reverse]. *)
  Definition type_of_reverse :=
    fn(∀ l : (list type); (l @ (list_t)); True)
      → ∃ () : (), ((rev l) @ (list_t)); True.

  (* Specifications for function [length]. *)
  Definition type_of_length :=
    fn(∀ (p, l) : loc * (list type); (p @ (&own (l @ (list_t)))); ⌜length l <= max_int size_t⌝)
      → ∃ () : (), ((length l) @ (int (size_t))); (p ◁ₗ (l @ (list_t))).

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ (p, l1, l2) : loc * (list type) * (list type); (p @ (&own (l1 @ (list_t)))), (l2 @ (list_t)); True)
      → ∃ () : (), (void); (p ◁ₗ ((l1 ++ l2) @ (list_t))).

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (l, p, n) : (list Z) * loc * Z; (p @ (&own ((l `at_type` int size_t) @ (list_t)))), (n @ (int (size_t))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (p ◁ₗ ((l `at_type` int size_t) @ (list_t))) ∗ ⌜b ↔ n ∈ l⌝.

  (* Specifications for function [rev_append]. *)
  Definition type_of_rev_append :=
    fn(∀ (p, l1, l2) : loc * (list type) * (list type); (l1 @ (list_t)), (p @ (&own (l2 @ (list_t)))); True)
      → ∃ () : (), (void); (p ◁ₗ (((rev l1) ++ l2) @ (list_t))).
End spec.

Typeclasses Opaque list_t_rec.
