From refinedc.typing Require Import typing.
From refinedc.examples.flags Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/flags.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Record Flags := mkFlags {
    flag1 : bool ;
    flag2 : bool ;
  }.

  Definition nat_encodes_flags n fs :=
    Z.testbit n 0 = flag1 fs ∧
    Z.testbit n 1 = flag2 fs ∧
    ∀ k, k > 1 → ¬ Z.testbit n k.

  (* Definition of type [flags]. *)
  Definition flags_rec : (Flags -d> typeO) → (Flags -d> typeO) := (λ self f,
    tyexists (λ n : nat,
    constrained (struct struct_flags [@{type}
      (n @ (int (u8)))
    ]) (
      ⌜nat_encodes_flags n f⌝
    ))
  )%I.
  Typeclasses Opaque flags_rec.

  Global Instance flags_rec_ne : Contractive flags_rec.
  Proof. solve_type_proper. Qed.

  Definition flags : rtype := {|
    rty_type := Flags;
    rty r__ := fixp flags_rec r__
  |}.

  Lemma flags_unfold (f : Flags):
    (f @ flags)%I ≡@{type} (
      tyexists (λ n : nat,
      constrained (struct struct_flags [@{type}
        (n @ (int (u8)))
      ]) (
        ⌜nat_encodes_flags n f⌝
      ))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance flags_rmovable : RMovable flags :=
    {| rmovable patt__ := movable_eq _ _ (flags_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance flags_simplify_hyp_place_inst l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (flags_unfold _)).
  Global Instance flags_simplify_goal_place_inst l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (flags_unfold _)).

  Global Program Instance flags_simplify_hyp_val_inst v_ patt__:
    SimplifyHypVal v_ (patt__ @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (flags_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance flags_simplify_goal_val_inst v_ patt__:
    SimplifyGoalVal v_ (patt__ @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (flags_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [sum]. *)
  Definition type_of_sum :=
    fn(∀ (fs, n1, n2) : Flags * nat * nat; (fs @ (flags)), (n1 @ (int (u32))), (n2 @ (int (u32))); ⌜n1 + n2 ≤ max_int u32⌝)
      → ∃ () : (), (((if flag1 fs then n1 else 0) + (if flag2 fs then n2 else 0)) @ (int (u32))); True.
End spec.

Typeclasses Opaque flags_rec.
