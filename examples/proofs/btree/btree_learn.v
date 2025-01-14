From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code generated_spec btree_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/btree/btree.c]. *)
Section learnable.
  Context `{!typeG Σ} `{!globalG Σ}.

  Global Program Instance btree_learnabke r l β : Learnable (l ◁ₗ{β} r @ btree_t)%I := {
    learnable_data := ⌜∃ n ks vs cs, btree_invariant ORDER r n ks vs cs⌝;
  }.
  Next Obligation.
    iIntros (r l β) "Hl". rewrite btree_t_unfold /ty_own /=.
    iDestruct "Hl" as ([[[n ks] vs] cs]) "Hl". rewrite tyexists_eq /persistent_own_constraint /=.
    rewrite /ty_own /=. iDestruct "Hl" as "[_ %]". iPureIntro. naive_solver.
  Qed.
End learnable.
