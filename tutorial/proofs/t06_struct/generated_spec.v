From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [color]. *)
  Definition color_rec : (nat * nat * nat -d> typeO) → (nat * nat * nat -d> typeO) := (λ self patt__,
    let r := patt__.1.1 in
    let g := patt__.1.2 in
    let b := patt__.2 in
    struct struct_color [@{type}
      (r @ (int (u8))) ;
      (g @ (int (u8))) ;
      (b @ (int (u8)))
    ]
  )%I.
  Typeclasses Opaque color_rec.

  Global Instance color_rec_ne : Contractive color_rec.
  Proof. solve_type_proper. Qed.

  Definition color : rtype := {|
    rty_type := nat * nat * nat;
    rty r__ := fixp color_rec r__
  |}.

  Lemma color_unfold (r : nat) (g : nat) (b : nat) :
    ((r, g, b) @ color)%I ≡@{type} (
      struct struct_color [@{type}
        (r @ (int (u8))) ;
        (g @ (int (u8))) ;
        (b @ (int (u8)))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance color_rmovable : RMovable color :=
    {| rmovable '(r, g, b) := movable_eq _ _ (color_unfold r g b) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance color_simplify_hyp_place_inst l_ β_ (r : nat) (g : nat) (b : nat) :
    SimplifyHypPlace l_ β_ ((r, g, b) @ color)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (color_unfold _ _ _)).
  Global Instance color_simplify_goal_place_inst l_ β_ (r : nat) (g : nat) (b : nat) :
    SimplifyGoalPlace l_ β_ ((r, g, b) @ color)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (color_unfold _ _ _)).

  Global Program Instance color_simplify_hyp_val_inst v_ (r : nat) (g : nat) (b : nat) :
    SimplifyHypVal v_ ((r, g, b) @ color)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (color_unfold _ _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance color_simplify_goal_val_inst v_ (r : nat) (g : nat) (b : nat) :
    SimplifyGoalVal v_ ((r, g, b) @ color)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (color_unfold _ _ _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [rgb]. *)
  Definition type_of_rgb :=
    fn(∀ (r, g, b) : nat * nat * nat; (r @ (int (u8))), (g @ (int (u8))), (b @ (int (u8))); True)
      → ∃ () : (), (((r, g, b)) @ (color)); True.

  (* Specifications for function [red]. *)
  Definition type_of_red :=
    fn(∀ r : nat; (r @ (int (u8))); True)
      → ∃ () : (), (((r, 0, 0)%nat) @ (color)); True.

  (* Specifications for function [green]. *)
  Definition type_of_green :=
    fn(∀ g : nat; (g @ (int (u8))); True)
      → ∃ () : (), (((0, g, 0)%nat) @ (color)); True.

  (* Specifications for function [blue]. *)
  Definition type_of_blue :=
    fn(∀ b : nat; (b @ (int (u8))); True)
      → ∃ () : (), (((0, 0, b)%nat) @ (color)); True.
End spec.

Typeclasses Opaque color_rec.