From refinedc.typing Require Export type.
From refinedc.typing Require Import programs own intptr singleton.
Set Default Proof Using "Type".

Section tagged_ptr.
  Context `{!typeG Σ}.

  Program Definition tagged_ptr_type (β : own_state) (align : nat) (ty : type) (r : loc * Z) : type := {|
    ty_own β' l :=
      ⌜l `has_layout_loc` void*⌝ ∗
      ⌜r.1 `aligned_to` align⌝ ∗
      ⌜0 ≤ r.2 < align⌝ ∗
      l ↦[β'] (r.1 +ₗ r.2) ∗
      loc_in_bounds r.1 align ∗
      r.1 ◁ₗ{own_state_min β' β} ty;
  |}%I.
  Next Obligation.
    iIntros (β ??????) "($&$&$&Hl&$&H)". rewrite left_id.
    iMod (heap_mapsto_own_state_share with "Hl") as "$".
    destruct β => //=. by iApply ty_share.
  Qed.
  Global Instance tagged_ptr_type_ne n : Proper ((=) ==> (dist n) ==> (=) ==> (=) ==> (dist n)) tagged_ptr_type.
  Proof. solve_type_proper. Qed.
  Global Instance tagged_ptr_type_proper : Proper ((=) ==> (≡) ==> (=) ==> (=) ==> (≡)) tagged_ptr_type.
  Proof. solve_type_proper. Qed.

  Program Definition tagged_ptr (β : own_state) (align : nat) (ty : type) : rtype := {|
    rty_type := loc * Z;
    rty := tagged_ptr_type β align ty;
  |}%I.

  Global Program Instance rmovable_tagged_ptr β align ty : RMovable (tagged_ptr β align ty) := {|
    rmovable r := {|
      ty_layout := void*;
      ty_own_val v :=
        ⌜v = val_of_loc (r.1 +ₗ r.2)⌝ ∗
        ⌜r.1 `aligned_to` align⌝ ∗
        ⌜0 ≤ r.2 < align⌝ ∗
        loc_in_bounds r.1 align ∗
        r.1 ◁ₗ{β} ty;
    |}
  |}%I.
  Next Obligation. iIntros (?????) "($&_)". Qed.
  Next Obligation. iIntros (?????) "(->&_)". done. Qed.
  Next Obligation. iIntros (?????) "(%&%&%&?&?)". rewrite left_id. eauto with iFrame. Qed.
  Next Obligation. iIntros (???????) "? (->&%&%&?)". iFrame. rewrite left_id. eauto with iFrame. Qed.
  Next Obligation. done. Qed.

  Global Instance tagged_ptr_loc_in_bounds r ty align β1 β2 :
    LocInBounds (r @ tagged_ptr β1 align ty) β2 bytes_per_addr.
  Proof.
    constructor. iIntros (?) "(_&_&_&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed.

  Global Instance tagged_ptr_related_to_frac_ptr v r β n ty:
     RelatedTo (v ◁ᵥ r @ tagged_ptr β n ty)%I | 1 :=
     {| rt_fic := FindValOrLoc v r.1 |}.

  Lemma subsume_tagged_ptr v r1 r2 n1 n2 β1 β2 ty1 ty2 T:
    (⌜r1 = r2⌝ ∗ ⌜n1 = n2⌝ ∗ ⌜β1 = β2⌝ ∗ subsume (r1.1 ◁ₗ{β1} ty1) (r2.1 ◁ₗ{β2} ty2) T) -∗
    subsume (v ◁ᵥ r1 @ tagged_ptr β1 n1 ty1) (v ◁ᵥ r2 @ tagged_ptr β2 n2 ty2) T.
  Proof.
    iIntros "(->&->&->&HT) ($&$&$&$&?)". by iApply "HT".
  Qed.
  Global Instance subsume_tagged_ptr_inst v r1 r2 n1 n2 β1 β2 ty1 ty2:
    SubsumeVal v (r1 @ tagged_ptr β1 n1 ty1) (r2 @ tagged_ptr β2 n2 ty2) :=
    λ T, i2p (subsume_tagged_ptr v r1 r2 n1 n2 β1 β2 ty1 ty2 T).

  Lemma subsume_frac_ptr_tagged_ptr l β (v : val) r n ty1 ty2 m T `{!LearnAlignment β ty1 m}:
    (⌜if m is Some m' then l `aligned_to` m' else True⌝ -∗
      ⌜l = r.1⌝ ∗ ⌜v = r.1 +ₗ r.2⌝ ∗ ⌜l `aligned_to` n⌝ ∗ ⌜0 ≤ r.2 < n⌝ ∗
     ((l ◁ₗ{β} ty1 -∗ loc_in_bounds l n ∗ True) ∧ subsume (l ◁ₗ{β} ty1) (l ◁ₗ{β} ty2) T)) -∗
    subsume (l ◁ₗ{β} ty1) (v ◁ᵥ r @ tagged_ptr β n ty2) T.
  Proof.
    iIntros "HT Hl".
    iDestruct (learnalign_learn with "Hl") as %?.
    iDestruct ("HT" with "[//]") as "(->&->&%&%&HT)".
    iAssert (loc_in_bounds r.1 n) as "#Hlib".
    { iDestruct "HT" as "[HT _]". iDestruct ("HT" with "Hl") as "[$ _]". }
    iDestruct "HT" as "[_ HT]". iDestruct ("HT" with "Hl") as "[$ $]". by iFrame "Hlib".
  Qed.
  Global Instance subsume_frac_ptr_tagged_ptr_inst l β v r n ty1 ty2 m `{!LearnAlignment β ty1 m}:
    Subsume (l ◁ₗ{β} ty1)%I (v ◁ᵥ r @ tagged_ptr β n ty2)%I :=
    λ T, i2p (subsume_frac_ptr_tagged_ptr l β v r n ty1 ty2 m T).

  Lemma simplify_hyp_tagged_ptr_0 v r β n ty `{!CanSolve (r.2 = 0)} T:
    (v ◁ᵥ r.1 @ frac_ptr β ty -∗ T) -∗
    simplify_hyp (v ◁ᵥ r @ tagged_ptr β n ty) T.
  Proof.
    unfold CanSolve in *. destruct r as [l ?]. simpl in *. simplify_eq.
    iIntros "HT (->&%&%&?&?)". iApply "HT". rewrite /= shift_loc_0. by iFrame.
  Qed.
  Global Instance simplify_hyp_tagged_ptr_0_inst v r β n ty `{!CanSolve (r.2 = 0)}:
    SimplifyHypVal v (r @ tagged_ptr β n ty) (Some 0%N) :=
    λ T, i2p (simplify_hyp_tagged_ptr_0 v r β n ty T).

  Lemma type_cast_tagged_ptr_intptr_val (v : val) (r : loc * Z) β (align : nat) it ty T:
    (
        ⌜v = r.1 +ₗ r.2⌝ -∗
        ⌜aligned_to r.1 align⌝ -∗
        ⌜0 ≤ r.2 < align⌝ -∗
        ⌜min_alloc_start ≤ r.1.2 ∧ r.1.2 + align ≤ max_alloc_end⌝ -∗
        loc_in_bounds r.1 align -∗
        r.1 ◁ₗ{β} ty -∗
        v ◁ᵥ r @ tagged_ptr β align (place r.1) -∗
        ⌜(r.1.2 + r.2)%Z ∈ it⌝ ∗
        ((alloc_alive_loc r.1 ∗ True) ∧
        T (val_of_loc_n (bytes_per_int it) (r.1 +ₗ r.2)) (t2mt ((r.1 +ₗ r.2) @ intptr it)))
    ) -∗
    typed_un_op v (v ◁ᵥ r @ tagged_ptr β align ty) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "HT (->&%&%&#Hlib&Hp)" (Φ) "HΦ".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %Hrange.
    iDestruct ("HT" with "[//] [//] [//] [//] [$] [$] []") as (Hr) "HT".
    { by iFrame "Hlib". }
    iApply wp_cast_ptr_int => //=; first by rewrite val_to_of_loc.
    { by rewrite bool_decide_true. }
    iSplit.
    { iDestruct "HT" as "[[HT _] _]". by iApply (alloc_alive_loc_mono with "HT"). }
    iDestruct "HT" as "[_ HT]". iApply ("HΦ" with "[] HT").
    iPureIntro. by apply val_to_loc_weak_val_of_loc_n.
  Qed.
  Global Instance type_cast_tagged_ptr_intptr_val_inst (v : val) (r : loc * Z) β (align : nat) it ty:
    TypedUnOp v (v ◁ᵥ r @ tagged_ptr β align ty)%I (CastOp (IntOp it)) PtrOp :=
    λ T, i2p (type_cast_tagged_ptr_intptr_val v r β align it ty T).

  Lemma type_copy_aid_tagged_ptr l1 β1 ty1 v2 r β2 ty2 align T:
    (l1 ◁ₗ{β1} ty1 -∗ v2 ◁ᵥ r @ tagged_ptr β2 align ty2 -∗
      ⌜r.1.2 ≤ l1.2 ≤ r.1.2 + align⌝ ∗
      ((alloc_alive_loc r.1 ∗ True) ∧
      T (val_of_loc (r.1.1, l1.2)) (t2mt (value void* (val_of_loc (r.1.1, l1.2)))))) -∗
    typed_copy_alloc_id l1 (l1 ◁ₗ{β1} ty1) v2 (v2 ◁ᵥ r @ tagged_ptr β2 align ty2) PtrOp T.
  Proof.
    iIntros "HT Hp1 (->&%&%&#Hlib&Hp)" (Φ) "HΦ".
    iDestruct ("HT" with "Hp1 [$Hlib $Hp]") as ([??]) "HT"; [done|].
    rewrite !right_id.
    iApply wp_copy_alloc_id; [ by rewrite val_to_of_loc | by rewrite val_to_of_loc |  | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done | done | etrans; [|done]; lia]. }
    iSplit.
    - iDestruct "HT" as "[Halloc _]". by iApply (alloc_alive_loc_mono with "Halloc").
    - iDestruct "HT" as "[_ HT]". by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_copy_aid_tagged_ptr_inst (l1 : loc) β1 ty1 v2 r β2 ty2 align:
    TypedCopyAllocId l1 (l1 ◁ₗ{β1} ty1) v2 (v2 ◁ᵥ r @ tagged_ptr β2 align ty2)%I PtrOp :=
    λ T, i2p (type_copy_aid_tagged_ptr l1 β1 ty1 v2 r β2 ty2 align T).
End tagged_ptr.
Typeclasses Opaque tagged_ptr_type.

Notation "tagged_ptr< β , align , ty >" :=
  (tagged_ptr β align ty)
  (only printing, format "'tagged_ptr<' β , align , ty '>'") : printing_sugar.
