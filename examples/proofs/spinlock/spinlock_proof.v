From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import generated_code generated_spec.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.
  Typeclasses Transparent spinlock spinlocked_ex spinlock_token spinlocked_ex_token.


  Lemma type_sl_init:
    ⊢ typed_function impl_sl_init type_of_sl_init.
  Proof.
    start_function "sl_init" (p) => vl. split_blocks (∅ : gmap label (iProp Σ)) (∅ : gmap label (iProp Σ)).

    iApply fupd_typed_stmt.
    iMod (own_alloc (● GSet ∅)) as (γ) "Hown". by apply auth_auth_valid.
    iAssert (spinlock_token γ []) with "[Hown]" as "?". iExists _. by iFrame.
    iModIntro.

    repeat liRStep; liShow.
    liInst Hevar γ.
    repeat liRStep; liShow.
    Unshelve. all: prepare_sideconditions; solve_goal.
  Qed.

  Lemma type_sl_lock:
    ⊢ typed_function impl_sl_lock type_of_sl_lock.
  Proof.
    start_function "sl_lock" ([[p γ] β]) => vl vexpected.
    split_blocks ({[ "#1" := vl ◁ₗ p @ &frac{β} (spinlock γ) ∗ vexpected ◁ₗ false @ boolean bool_it ]}%I : gmap label (iProp Σ)) (∅ : gmap label (iProp Σ)).

    - repeat liRStep; liShow.
    - repeat liRStep; liShow.
      Unshelve. all: prepare_sideconditions; try solve_goal.
      rewrite /bytes_per_int/=. have ->: bytes_per_addr = 8%nat; solve_goal.
  Qed.

  Lemma type_sl_unlock:
    ⊢ typed_function impl_sl_unlock type_of_sl_unlock.
  Proof.
    start_function "sl_unlock" ([[p γ] β]) => vl. split_blocks (∅ : gmap label (iProp Σ)) (∅ : gmap label (iProp Σ)).

    repeat liRStep; liShow.
    Unshelve. all: prepare_sideconditions; solve_goal.
  Qed.

End type.
