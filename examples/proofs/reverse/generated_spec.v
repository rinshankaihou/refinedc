From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [list_t]. *)
  Definition list_t_rec : ((list type) → type) → ((list type) → type) := (λ self l,
    ((maybe2 cons l) @ (optionalO (λ patt__,
      let ty := patt__.1 in
      let l := patt__.2 in
      &own (
        struct struct_list [@{type}
          (&own (ty)) ;
          (self (l))
        ]
      )
    ) null))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype ((list type)) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (l : (list type)):
    (l @ list_t)%I ≡@{type} (
      ((maybe2 cons l) @ (optionalO (λ patt__,
        let ty := patt__.1 in
        let l := patt__.2 in
        &own (
          struct struct_list [@{type}
            (&own (ty)) ;
            (l @ list_t)
          ]
        )
      ) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 list_t_rec). Qed.

  Definition list_t_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_place_inst_generated.
  Definition list_t_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_place_inst_generated.

  Definition list_t_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_hyp_val_inst_generated.
  Definition list_t_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (list_t_unfold patt__) with 100%N].
  Global Existing Instance list_t_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

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
      → ∃ b : bool, (b @ (builtin_boolean)); (p ◁ₗ ((l `at_type` int size_t) @ (list_t))) ∗ ⌜b ↔ n ∈ l⌝.

  (* Specifications for function [member]. *)
  Definition type_of_member :=
    fn(∀ (l, p, n) : (list Z) * loc * Z; (p @ (&own ((l `at_type` int size_t) @ (list_t)))), (n @ (int (size_t))); True)
      → ∃ b : bool, (b @ (builtin_boolean)); (p ◁ₗ ((l `at_type` int size_t) @ (list_t))) ∗ ⌜b ↔ n ∈ l⌝.

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

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
