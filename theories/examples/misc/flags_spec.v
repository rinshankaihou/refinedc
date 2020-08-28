From refinedc.typing Require Import typing.
From refinedc.examples.misc Require Import flags_code.
Set Default Proof Using "Type".

(* Generated from [theories/examples/misc/flags.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition flags_type := (bool * bool * bool)%type.

  Definition flags_from_nat n :=
    let b0 := bool_decide (n `mod` 2 = 1) in
    let n  := n `div` 2 in
    let b1 := bool_decide (n `mod` 2 = 1) in
    let n  := n `div` 2 in
    let b2 := bool_decide (n `mod` 2 = 1) in
    let n  := n `div` 2 in
    if bool_decide (n = 0) then Some (b0, b1, b2) else None.

  (* Definition of type [flags]. *)
  Definition flags_rec : (flags_type -d> typeO) → (flags_type -d> typeO) := (λ self f,
    tyexists (λ n : nat,
    constrained (struct struct_flags [@{type}
      (n @ (int (u8)))
    ]) (
      ⌜flags_from_nat n = Some f⌝
    ))
  )%I.
  Typeclasses Opaque flags_rec.

  Global Instance flags_rec_ne : Contractive flags_rec.
  Proof. solve_type_proper. Qed.

  Definition flags : rtype := {|
    rty_type := flags_type;
    rty r__ := fixp flags_rec r__
  |}.

  Lemma flags_unfold (f : flags_type) :
    (f @ flags)%I ≡@{type} (
      tyexists (λ n : nat,
      constrained (struct struct_flags [@{type}
        (n @ (int (u8)))
      ]) (
        ⌜flags_from_nat n = Some f⌝
      ))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance flags_rmovable : RMovable flags :=
    {| rmovable 'f := movable_eq _ _ (flags_unfold f) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance flags_simplify_hyp_place_inst l_ β_ (f : flags_type) :
    SimplifyHypPlace l_ β_ (f @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (flags_unfold _)).
  Global Instance flags_simplify_goal_place_inst l_ β_ (f : flags_type) :
    SimplifyGoalPlace l_ β_ (f @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (flags_unfold _)).

  Global Program Instance flags_simplify_hyp_val_inst v_ (f : flags_type) :
    SimplifyHypVal v_ (f @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (flags_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance flags_simplify_goal_val_inst v_ (f : flags_type) :
    SimplifyGoalVal v_ (f @ flags)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (flags_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [sum]. *)
  Definition type_of_sum :=
    fn(∀ (f1, f2, f3, n1, n2, n3) : bool * bool * bool * nat * nat * nat; (((f1, f2, f3)) @ (flags)), (n1 @ (int (u32))), (n2 @ (int (u32))), (n3 @ (int (u32))); ⌜n1 + n2 < it_max u32⌝ ∗ ⌜n2 + n3 < it_max u32⌝ ∗ ⌜n1 + n3 < it_max u32⌝ ∗ ⌜n1 + n2 + n3 < it_max u32⌝)
      → ∃ () : (), (((if f1 then n1 else 0) + (if f2 then n2 else 0) + (if f3 then n3 else 0)) @ (int (u32))); True.
End spec.

Typeclasses Opaque flags_rec.
