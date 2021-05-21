From refinedc.typing Require Export type.
From refinedc.typing Require Import programs own singleton int.
Set Default Proof Using "Type".

Section intptr.
  Context `{!typeG Σ}.

  Program Definition intptr_inner_type (it : int_type) (p : loc) : type := {|
    ty_own β l := ∃ v, ⌜val_to_loc_weak v it = Some p⌝ ∗ ⌜l `has_layout_loc` it⌝ ∗ l ↦[β] v;
  |}%I.
  Next Obligation.
    iIntros (it n l ??) "(%v&%Hv&%Hl&H)". iExists v.
    do 2 (iSplitR; first done). by iApply heap_mapsto_own_state_share.
  Qed.

  Program Definition intptr (it : int_type) : rtype := {|
    rty_type := loc;
    rty := intptr_inner_type it;
  |}.

  Global Program Instance rmovable_intptr it : RMovable (intptr it) := {|
    rmovable l := {|
      ty_layout := it_layout it;
      ty_own_val v := ⌜val_to_loc_weak v it = Some l⌝;
    |}
  |}%I.
  Next Obligation. iIntros (???) "(%&%&$&_)". Qed.
  Next Obligation. iIntros (??? H) "!%". by apply val_to_loc_weak_length in H. Qed.
  Next Obligation. iIntros (???) "(%v&%&%&Hl)". eauto with iFrame. Qed.
  Next Obligation. iIntros (??? v ?) "Hl %". iExists v. eauto with iFrame. Qed.
  Next Obligation. iIntros (???). done. Qed.

  Lemma intptr_loc_in_bounds l β p it:
     l ◁ₗ{β} p @ intptr it -∗ loc_in_bounds l (bytes_per_int it).
  Proof.
    iIntros "(%&%Hv&%&Hl)". move: Hv => /val_to_loc_weak_length <-.
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.

  Global Instance loc_in_bounds_intptr p it β: LocInBounds (p @ intptr it) β (bytes_per_int it).
  Proof.
    constructor. iIntros (l) "Hl".
    iDestruct (intptr_loc_in_bounds with "Hl") as "Hlib".
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.

  Lemma ty_own_intptr_in_range l β p it : l ◁ₗ{β} p @ intptr it -∗ ⌜p.2 ∈ it⌝.
  Proof.
    iIntros "Hl". destruct β.
    - iDestruct (ty_deref with "Hl") as (?) "[_ %]".
      iPureIntro. by eapply val_to_loc_weak_in_range.
    - iDestruct "Hl" as (?) "[% _]".
      iPureIntro. by eapply val_to_loc_weak_in_range.
  Qed.

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance intptr_copyable p it : Copyable (p @ intptr it).
  Next Obligation.
    iIntros (?????) "(%v&%Hv&%Hl&Hl)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iSplitR => //. iExists q, v. iFrame. iModIntro. eauto with iFrame.
  Qed.

  Global Instance intptr_timeless l p it:
    Timeless (l ◁ₗ p @ intptr it)%I.
  Proof. apply _. Qed.

End intptr.
(* Typeclasses Opaque int. *)
Notation "intptr< it >" := (intptr it) (only printing, format "'intptr<' it '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ}.

  Lemma type_cast_ptr_intptr (p : loc) β it ty n `{!LocInBounds ty β n} T:
    ((⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end → p.2 ∈ it⌝) ∗ (
        ⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end⌝ -∗
        p ◁ₗ{β} ty -∗
        T (val_of_loc_n (bytes_per_int it) p) (t2mt (p @ intptr it)))
    ) -∗
    typed_un_op p (p ◁ₗ{β} ty) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "[%Hin HT] Hp" (Φ) "HΦ".
    iDestruct (loc_in_bounds_in_bounds with "Hp") as "#Hlib".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %?.
    iDestruct ("HT" with "[] Hp") as "HT"; first done.
    iApply wp_cast_ptr_int => //=; first by rewrite val_to_of_loc.
    { rewrite bool_decide_true; naive_solver. }
    iApply ("HΦ" with "[] [HT]"); last done.
    iPureIntro. apply val_to_loc_weak_val_of_loc_n. naive_solver.
  Qed.
  Global Instance type_cast_ptr_intptr_inst (p : loc) β it ty n `{!LocInBounds ty β n}:
    TypedUnOp p (p ◁ₗ{β} ty)%I (CastOp (IntOp it)) PtrOp :=
    λ T, i2p (type_cast_ptr_intptr p β it ty n T).

  Lemma type_cast_ptr_intptr_val (v : val) (p : loc) it (n : nat) T:
    ((⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end → p.2 ∈ it⌝) ∗ (
        ⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end⌝ -∗
        v ◁ᵥ p @ ptr n -∗
        T (val_of_loc_n (bytes_per_int it) p) (t2mt (p @ intptr it)))
    ) -∗
    typed_un_op v (v ◁ᵥ p @ ptr n) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "[%Hin HT] [-> #Hlib]" (Φ) "HΦ".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %?.
    iDestruct ("HT" with "[//] []") as "HT". { by iFrame "Hlib". }
    iApply wp_cast_ptr_int => //=; first by rewrite val_to_of_loc.
    { rewrite bool_decide_true; naive_solver. }
    iApply ("HΦ" with "[] [HT]"); last done.
    iPureIntro. apply val_to_loc_weak_val_of_loc_n. naive_solver.
  Qed.
  Global Instance type_cast_ptr_intptr_val_inst (v : val) (p : loc) it (n : nat):
    TypedUnOp v (v ◁ᵥ p @ ptr n)%I (CastOp (IntOp it)) PtrOp :=
    λ T, i2p (type_cast_ptr_intptr_val v p it n T).

  Lemma type_cast_intptr_ptr p v it T:
    (T (val_of_loc p) (t2mt (p @ frac_ptr Own (place p)))) -∗
    typed_un_op v (v ◁ᵥ p @ intptr it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    iIntros "HT" (Hn Φ) "HΦ".
    iApply wp_cast_int_ptr => //.
    iApply ("HΦ" with "[]"); last iApply "HT". done.
  Qed.
  Global Instance type_cast_intptr_ptr_inst p v it:
    TypedUnOp v (v ◁ᵥ p @ intptr it)%I (CastOp PtrOp) (IntOp it) :=
    λ T, i2p (type_cast_intptr_ptr p v it T).

  Lemma type_copy_aid_intptr v1 P1 v2 p2 it T:
    (∃ p1,
      subsume P1 (v1 ◁ᵥ p1 @ frac_ptr Own (place p1)) (
        T (val_of_loc (p2.1, p1.2)) (t2mt (value void* (val_of_loc (p2.1, p1.2))))
      )
    ) -∗
    typed_copy_alloc_id v1 P1 v2 (v2 ◁ᵥ p2 @ intptr it) (IntOp it) T.
  Proof.
    iIntros "HT Hp1 Hp2" (Φ) "HΦ". iDestruct "HT" as (p1) "HT".
    iDestruct ("HT" with "Hp1") as "[Hp1 HT]". iDestruct "Hp1" as (->) "Hp1".
    iDestruct "Hp2" as %Hp2.
    iApply wp_copy_alloc_id_int => //; first by rewrite val_to_of_loc.
    by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_copy_aid_intptr_inst v1 P1 v2 p2 it:
    TypedCopyAllocId v1 P1 v2 (v2 ◁ᵥ p2 @ intptr it)%I (IntOp it) :=
    λ T, i2p (type_copy_aid_intptr v1 P1 v2 p2 it T).

  Lemma intptr_wand_int v p it:
    v ◁ᵥ p @ intptr it -∗ v ◁ᵥ p.2 @ int it.
  Proof.
    iPureIntro. rewrite /val_to_loc_weak /val_to_Z_weak.
    move => /fmap_Some [i][-> ->]. by destruct i.
  Qed.

  Lemma subsume_intptr_int_val v it (n : Z) (p : loc) T:
    ⌜n = p.2⌝ ∗ T -∗
    subsume (v ◁ᵥ p @ intptr it) (v ◁ᵥ n @ int it) T.
  Proof.
    iIntros "[-> $]". iApply intptr_wand_int.
  Qed.
  Global Instance subsume_intptr_int_val_inst v it n p:
    SubsumeVal v (p @ intptr it) (n @ int it) :=
    λ T, i2p (subsume_intptr_int_val v it n p T).

  Lemma subsume_intptr_int_place l β it n p T:
    ⌜n = p.2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} p @ intptr it) (l ◁ₗ{β} n @ int it) T.
  Proof.
    iIntros "[-> $]". rewrite /ty_own /=. iIntros "(%v&H&?&?)".
    iExists v. iFrame. iRevert "H". iPureIntro.
    rewrite /val_to_loc_weak /val_to_Z_weak.
    move => /fmap_Some [i][-> ->] /=. by destruct i.
  Qed.
  Global Instance subsume_intptr_int_place_inst l β it n p:
    SubsumePlace l β (p @ intptr it) (n @ int it) :=
    λ T, i2p (subsume_intptr_int_place l β it n p T).

  Lemma typed_un_op_intptr it v l op T:
    typed_un_op v (v ◁ᵥ l.2 @ int    it) op (IntOp it) T -∗
    typed_un_op v (v ◁ᵥ l   @ intptr it) op (IntOp it) T.
  Proof.
    iApply typed_un_op_wand. iApply intptr_wand_int.
  Qed.
  Global Instance typed_un_op_intptr_inst it v l op:
    TypedUnOpVal v (l @ intptr it)%I op (IntOp it) :=
    λ T, i2p (typed_un_op_intptr it v l op T).

  Lemma typed_bin_op_intptr_l it v1 l v2 ty op ot `{!Movable ty} T:
    typed_bin_op v1 (v1 ◁ᵥ l.2 @ int    it) v2 (v2 ◁ᵥ ty) op (IntOp it) ot T -∗
    typed_bin_op v1 (v1 ◁ᵥ l   @ intptr it) v2 (v2 ◁ᵥ ty) op (IntOp it) ot T.
  Proof.
    iApply typed_bin_op_wand; last by iIntros "$".
    iApply intptr_wand_int.
  Qed.
  Global Instance typed_bin_op_intptr_l_inst it v1 l v2 ty op ot `{!Movable ty}:
    TypedBinOpVal v1 (l @ intptr it)%I v2 ty op (IntOp it) ot :=
    λ T, i2p (typed_bin_op_intptr_l it v1 l v2 ty op ot T).

  Lemma typed_bin_op_intptr_r it v1 ty v2 l op ot `{!Movable ty} T:
    typed_bin_op v1 (v1 ◁ᵥ ty) v2 (v2 ◁ᵥ l.2 @ int    it) op ot (IntOp it) T -∗
    typed_bin_op v1 (v1 ◁ᵥ ty) v2 (v2 ◁ᵥ l   @ intptr it) op ot (IntOp it) T.
  Proof.
    iApply typed_bin_op_wand; first by iIntros "$".
    iApply intptr_wand_int.
  Qed.
  Global Instance typed_bin_op_intptr_r_inst it v1 ty v2 l op ot `{!Movable ty}:
    TypedBinOpVal v1 ty v2 (l @ intptr it)%I op ot (IntOp it) :=
    λ T, i2p (typed_bin_op_intptr_r it v1 ty v2 l op ot T).

End programs.
Typeclasses Opaque intptr_inner_type.
