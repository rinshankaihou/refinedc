From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import reverse_code.
Set Default Proof Using "Type".

(* Generated from [theories/examples/reverse/reverse.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

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

  (* Specifications for function [init]. *)
  Definition type_of_init :=
    fn(∀ () : (); True) → ∃ () : (), (([]) @ (list_t)); True.

  (* Specifications for function [push]. *)
  Definition type_of_push :=
    fn(∀ (l, ty) : (list type) * type; (l @ (list_t)), (&own (ty)), (&own (uninit (struct_list))); True)
      → ∃ () : (), ((ty :: l) @ (list_t)); True.

  (* Specifications for function [pop]. *)
  Definition type_of_pop :=
    fn(∀ (l, p) : (list type) * loc; (p @ (&own ((l) @ (list_t)))); True)
      → ∃ () : (), ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (ty) ) null)); (p ◁ₗ ((tail l) @ (list_t))).

  (* Specifications for function [member_rec]. *)
  Definition type_of_member_rec :=
    fn(∀ (l, p, n) : (list Z) * loc * Z; (p @ (&own ((l `at_type` int size_t) @ (list_t)))), (n @ (int (size_t))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (p ◁ₗ ((l `at_type` int size_t) @ (list_t))) ∗ ⌜b ↔ n ∈ l⌝.

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (l, p, n) : (list Z) * loc * Z; (p @ (&own ((l `at_type` int size_t) @ (list_t)))), (n @ (int (size_t))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (p ◁ₗ ((l `at_type` int size_t) @ (list_t))) ∗ ⌜b ↔ n ∈ l⌝.

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜True⌝.

  (* Specifications for function [reverse]. *)
  Definition type_of_reverse :=
    fn(∀ l : (list type); (l @ (list_t)); True)
      → ∃ () : (), ((rev l) @ (list_t)); True.

  (* Specifications for function [forward]. *)
  Definition type_of_forward :=
    fn(∀ l : (list type); (l @ (list_t)); True)
      → ∃ () : (), (l @ (list_t)); True.
End spec.

Typeclasses Opaque list_t_rec.
