From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo2 Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo2.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Definition of type [list_t]. *)
  Definition list_t_rec : (unit → type) → (unit → type) := (λ self x__,
    (optionalO (λ _ : unit,
      &own (
        struct struct_list_node [@{type}
          (int (i32)) ;
          (tyexists (λ rfmt__, self (rfmt__)))
        ]
      )
    ) (null))
  )%I.
  Global Typeclasses Opaque list_t_rec.

  Global Instance list_t_rec_le : TypeMono list_t_rec.
  Proof. solve_type_proper. Qed.

  Definition list_t : rtype (unit) := {|
    rty r__ := list_t_rec (type_fixpoint list_t_rec) r__
  |}.

  Lemma list_t_unfold (x__ : unit):
    (x__ @ list_t)%I ≡@{type} (
      (optionalO (λ _ : unit,
        &own (
          struct struct_list_node [@{type}
            (int (i32)) ;
            (tyexists (λ rfmt__, rfmt__ @ list_t))
          ]
        )
      ) (null))
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

  (* Specifications for function [safe_exit]. *)
  Definition type_of_safe_exit :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜False⌝.

  (* Specifications for function [malloc]. *)
  Definition type_of_malloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (optionalO (λ _ : unit,
        &own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))
      ) (null)); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ n : Z; (&own (malloced_early (n) (uninit (ly_max_align (Z.to_nat n))))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [xmalloc]. *)
  Definition type_of_xmalloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (&own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))); True.

  (* Specifications for function [append]. *)
  Definition type_of_append :=
    fn(∀ () : (); (&own (list_t)), (list_t); True)
      → ∃ () : (), (void); True.

  (* Function [test] has been skipped. *)
End spec.

Global Typeclasses Opaque list_t_rec.
Global Typeclasses Opaque list_t.
