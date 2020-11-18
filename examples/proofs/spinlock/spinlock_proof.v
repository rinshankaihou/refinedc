From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import generated_code generated_spec.
Set Default Proof Using "Type".

Typeclasses Transparent spinlock spinlocked_ex spinlock_token spinlocked_ex_token.

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.


  Lemma type_sl_init:
    ⊢ typed_function impl_sl_init type_of_sl_init.
  Proof.
    start_function "sl_init" (p) => vl. split_blocks (∅ : gmap label (iProp Σ)) (∅ : gmap label (iProp Σ)).

    iApply fupd_typed_stmt.
    iMod (own_alloc (● GSet ∅)) as (γ) "Hown"; [ by apply auth_auth_valid |].
    iAssert (spinlock_token γ []) with "[Hown]" as "?"; [ by iExists _; iFrame |].
    iModIntro.

    repeat liRStep; liShow.
    liInst Hevar γ.
    repeat liRStep; liShow.
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
  Qed.

End type.
