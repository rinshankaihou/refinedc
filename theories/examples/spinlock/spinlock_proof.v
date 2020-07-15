From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import spinlock_spec.
From refinedc.examples.spinlock Require Import spinlock_code.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.
  Typeclasses Transparent spinlock spinlocked_ex spinlock_token spinlocked_ex_token.

  Lemma type_sl_init:
    ⊢ typed_function impl_sl_init type_of_sl_init.
  Proof.
    start_function "sl_init" (p) => vl. split_blocks (∅ : gmap block_id (iProp Σ)) (∅ : gmap block_id (iProp Σ)).

    iApply fupd_typed_stmt.
    iMod (own_alloc (● GSet ∅)) as (γ) "Hown". by apply auth_auth_valid.
    iModIntro.

    repeat liRStep; liShow.
    iIntros "?". rewrite /(ty_own (spinlock _))/=.
    liInst Hevar γ.
    repeat liRStep; liShow.
    iSplitL => //. iExists _. by iFrame.
    Unshelve. all: prepare_sideconditions; solve_goal.
  Qed.

  Lemma type_sl_lock:
    ⊢ typed_function impl_sl_lock type_of_sl_lock.
  Proof.
    start_function "sl_lock" ([[p γ] β]) => vl vexpected.
    split_blocks ({[ "#1" := vl ◁ₗ p @ &frac{β} (spinlock γ) ∗ vexpected ◁ₗ false @ boolean bool_it ]}%I : gmap block_id (iProp Σ)) (∅ : gmap block_id (iProp Σ)).

    - repeat liRStep; liShow.
    - repeat liRStep; liShow.
      iApply typed_place_subsume'.
      destruct β.
      + iDestruct 1 as (b) "[? ?]".
        repeat liRStep; liShow.
        iIntros "H1 H2 H3" (Φ) "HΦ".
        iDestruct "H1" as (_) "H1".
        iDestruct "H2" as (_) "H2".
        (* TODO: don't unfold here *)
        rewrite {2 3}/boolean/boolean_inner_type/int_inner_type/=.
        iDestruct "H1" as (vo Hvo Hlo) "Ho" => /=. iDestruct "H2" as (ve Hve Hle) "He" => /=.
        destruct b.
        * iApply (wp_cas_fail with "Ho He"); try by [apply val_to_of_loc]; try by [apply val_to_of_int].
          all: try by rewrite // /loc_size/loc_size_log/it_length/it_size/=; lia.
          iIntros "!# Hvo Hve".
          iApply ("HΦ" $! _ (t2mt (Z_of_bool false @ int bool_it))%I with "[]") => //.
          iAssert (p at{struct_spinlock}ₗ "lock" ◁ₗ true @ boolean u8)%I with "[Hvo]" as "Hp". by iExists _; iFrame.
          iAssert (vexpected ◁ₗ true @ boolean u8)%I with "[Hve]" as "He". by iExists _; iFrame.
          repeat liRStep; liShow.
          iIntros "?". rewrite /(ty_own (spinlock _))/=.
          repeat liRStep; liShow.
        * iApply (wp_cas_suc with "Ho He"); try by [apply val_to_of_loc]; try by [apply val_to_of_int].
          all: try by rewrite // /loc_size/loc_size_log/it_length/it_size/=; lia.
          iIntros "!# Hvo Hve".
          iApply ("HΦ" $! _ (t2mt (Z_of_bool true @ int bool_it))%I with "[]") => //.
          iAssert (p at{struct_spinlock}ₗ "lock" ◁ₗ true @ boolean u8)%I with "[Hvo]" as "Hp". by iExists _; iFrame.
          iAssert (vexpected ◁ₗ false @ boolean u8)%I with "[Hve]" as "He". by iExists _; iFrame.
          repeat liRStep; liShow.
          iIntros "?". rewrite /(ty_own (spinlock _))/=.
          repeat liRStep; liShow.
      + iIntros "[% [#? #Hinv]]".
        repeat liRStep; liShow.
        iIntros "H1 H2 H3" (Φ) "HΦ". iDestruct "H2" as (_) "H2".
        (* TODO: don't unfold here *)
        rewrite {2}/boolean/boolean_inner_type/int_inner_type/=. iDestruct "H2" as (ve Hve Hle) "He" => /=.
        iApply (@wp_atomic).
        iMod (inv_acc with "Hinv") as "[Hb Hc]" => //. iModIntro.
        iDestruct "Hb" as (b) "[>Hmt Hown]".
        destruct b.
        * iApply (wp_cas_fail with "Hmt He"); try by [apply val_to_of_loc]; try by [apply val_to_of_int]; try by [apply val_to_int_bool].
          all: try by rewrite // /loc_size/loc_size_log/it_length/it_size/=; lia.
          iIntros "!# Hl He".
          iMod ("Hc" with "[Hl]") as "_"; iModIntro. by iExists _; iFrame.
          iApply ("HΦ" $! _ (t2mt (Z_of_bool false @ int bool_it))%I with "[]") => //.
          iAssert (vexpected ◁ₗ true @ boolean u8)%I with "[He]" as "He". by iExists _; iFrame.
          repeat liRStep; liShow.
          iIntros "?". rewrite /(ty_own (spinlock _))/=.
          repeat liRStep; liShow.
        * iApply (wp_cas_suc with "Hmt He"); try by [apply val_to_of_loc]; try by [apply val_to_of_int]; try by [apply val_to_int_bool].
          all: try by rewrite // /loc_size/loc_size_log/it_length/it_size/=; lia.
          iIntros "!# Hl He".
          iMod ("Hc" with "[Hl]") as "_"; iModIntro. rewrite/val_of_bool. by iExists true => /=; iFrame.
          iApply ("HΦ" $! _ (t2mt (Z_of_bool true @ int bool_it))%I with "[]") => //.
          iAssert (vexpected ◁ₗ false @ boolean u8)%I with "[He]" as "He". by iExists _; iFrame.
          repeat liRStep; liShow.
          iIntros "?". rewrite /(ty_own (spinlock _))/=.
          repeat liRStep; liShow.
          Unshelve. all: prepare_sideconditions; solve_goal.
  Qed.

  Lemma type_sl_unlock:
    ⊢ typed_function impl_sl_unlock type_of_sl_unlock.
  Proof.
    start_function "sl_unlock" ([[p γ] β]) => vl. split_blocks (∅ : gmap block_id (iProp Σ)) (∅ : gmap block_id (iProp Σ)).

    repeat liRStep; liShow.
    iApply typed_place_subsume'.
    destruct β.
    - iDestruct 1 as (b) "[? ?]".
      repeat liRStep; liShow.
      iIntros "?". rewrite /(ty_own (spinlock _))/=.
      repeat liRStep; liShow.
    - iIntros "[% [#? #Hinv]]".
      repeat liRStep; liShow.
      iExists (_, singleton_place _)%I => /=. iSplit => //.
      iIntros "_" => /=.
      iMod (inv_acc with "Hinv") as "[Hl Hc]" => //.
      iDestruct "Hl" as (b) "[>Hb Hown]".
      iMod (fupd_intro_mask') as "Hmask". 2: iModIntro. solve_ndisj.
      iSplitL "Hb". by iExists _; iFrame; iPureIntro; destruct b.
      iIntros "!# Hp _".
      iMod "Hmask" as "_". iMod ("Hc" with "[-]"). rewrite /val_of_bool. by iModIntro; iExists false; iFrame.
      iIntros "!#". iExists (singleton_place (p at{struct_spinlock}ₗ "lock"))%I. iSplit => //.
      repeat liRStep; liShow.
      iIntros "?". rewrite /(ty_own (spinlock _))/=.
      repeat liRStep; liShow.
      Unshelve. all: prepare_sideconditions; solve_goal.
  Qed.

End type.
