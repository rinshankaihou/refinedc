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
  Definition flags_rec : (Flags → type) → (Flags → type) := (λ self f,
    ∃ₜ (n : nat),
    constrained (struct struct_flags [@{type}
      (n @ (int (u8)))
    ]) (
      ⌜nat_encodes_flags n f⌝
    )
  )%I.
  Global Typeclasses Opaque flags_rec.

  Global Instance flags_rec_le : TypeMono flags_rec.
  Proof. solve_type_proper. Qed.

  Definition flags : rtype (Flags) := {|
    rty r__ := flags_rec (type_fixpoint flags_rec) r__
  |}.

  Lemma flags_unfold (f : Flags):
    (f @ flags)%I ≡@{type} (
      ∃ₜ (n : nat),
      constrained (struct struct_flags [@{type}
        (n @ (int (u8)))
      ]) (
        ⌜nat_encodes_flags n f⌝
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 flags_rec). Qed.

  Definition flags_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (flags_unfold patt__) with 100%N].
  Global Existing Instance flags_simplify_hyp_place_inst_generated.
  Definition flags_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (flags_unfold patt__) with 100%N].
  Global Existing Instance flags_simplify_goal_place_inst_generated.

  Definition flags_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (flags_unfold patt__) with 100%N].
  Global Existing Instance flags_simplify_hyp_val_inst_generated.
  Definition flags_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (flags_unfold patt__) with 100%N].
  Global Existing Instance flags_simplify_goal_val_inst_generated.

  (* Specifications for function [sum]. *)
  Definition type_of_sum :=
    fn(∀ (fs, n1, n2) : Flags * nat * nat; (fs @ (flags)), (n1 @ (int (u32))), (n2 @ (int (u32))); ⌜n1 + n2 ≤ max_int u32⌝)
      → ∃ () : (), (((if flag1 fs then n1 else 0) + (if flag2 fs then n2 else 0)) @ (int (u32))); True.
End spec.

Global Typeclasses Opaque flags_rec.
Global Typeclasses Opaque flags.
