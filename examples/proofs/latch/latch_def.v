From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code generated_spec.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ}.

  Definition LATCH_INIT := val_of_bool false.

  Lemma latch_init l E P:
    ↑shrN ⊆ E →
    l `has_layout_loc` struct_latch →
    l ↦ LATCH_INIT ={E}=∗ l ◁ₗ{Shr} P @ latch.
  Proof.
    iIntros (? ?) "Hl". iApply ty_share => //.
    unshelve iApply (@ty_ref  with "[] Hl").
    { apply: (UntypedOp struct_latch). }
    { apply: MCNone. }
    { solve_goal. }
    { done. }
    rewrite /ty_own_val/=. repeat iSplit => //.
    unfold atomic_bool; simpl_type. iExists false.
    unfold boolean; simpl_type. iSplit => //.
    by iExists _.
  Qed.
End type.
