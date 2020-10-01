From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code.
Set Default Proof Using "Type".

Definition latchN : namespace := nroot.@"lockN".

Section type.
  Context `{!typeG Σ}.

  Definition latch (P : iProp Σ) : type :=
    struct struct_latch [atomic_bool bool_it (□ P) True].

  Global Program Instance movable_latch P : Movable (latch P) := ltac:(apply: movable_struct).

  Lemma latch_simplify_hyp l β P T:
    (l ◁ₗ{β} struct struct_latch [atomic_bool bool_it (□ P) True] -∗ T) -∗
    simplify_hyp (l ◁ₗ{β} latch P) T.
  Proof. done. Qed.
  Global Instance latch_simplify_hyp_inst l β P:
    SimplifyHypPlace l β (latch P) (Some 100%N) :=
    λ T, i2p (latch_simplify_hyp l β P T).

  Lemma latch_simplify_goal l β P T:
    T (l ◁ₗ{β} struct struct_latch [atomic_bool bool_it (□ P) True]) -∗
    simplify_goal (l ◁ₗ{β} latch P) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "$". Qed.
  Global Instance latch_simplify_goal_inst l β P:
    SimplifyGoalPlace l β (latch P) (Some 100%N) :=
    λ T, i2p (latch_simplify_goal l β P T).

  Lemma latch_subsume P1 P2 l T β:
    ⌜P1 = P2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} latch P1) (l ◁ₗ{β} latch P2) T.
  Proof. iIntros "[-> $] $". Qed.
  Global Instance latch_subsume_inst P1 P2 l β:
    Subsume (l ◁ₗ{β} latch P1) (l ◁ₗ{β} latch P2) :=
    λ T, i2p (latch_subsume P1 P2 l T β).

  Definition LATCH_INIT := val_of_bool false.

  Lemma latch_init l E P:
    ↑shrN ⊆ E →
    l `has_layout_loc` struct_latch →
    l ↦ LATCH_INIT ={E}=∗ l ◁ₗ{Shr} latch P.
  Proof.
    iIntros (? ?) "Hl".
    iApply ty_share => //. iApply (ty_ref with "[] Hl") => //.
    rewrite /ty_own_val/=. repeat iSplit => //. rewrite /ty_own_val/=/ty_own_val/=. by iExists false.
  Qed.
End type.

Typeclasses Opaque latch.
