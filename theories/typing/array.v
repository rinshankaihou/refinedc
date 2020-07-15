From iris.algebra Require Import list.
From refinedc.typing Require Export type.
From refinedc.typing Require Import programs singleton uninit int.
Set Default Proof Using "Type".

Section type.
  Context `{typeG Σ}.
  (*** arrays *)
  (*** array *)
  Program Definition array (ly : layout) (tys : list type) : type := {|
    ty_own β l := (⌜l `has_layout_loc` ly⌝ ∗ [∗ list] i ↦ ty ∈ tys, (l offset{ly}ₗ i) ◁ₗ{β} ty)%I
  |}.
  Next Obligation.
    iIntros (ly tys l E He) "[$ Ha]". iApply big_sepL_fupd. iApply (big_sepL_impl with "Ha").
    iIntros "!#" (???). by iApply ty_share.
  Qed.

  Global Instance array_ne n : Proper ((=) ==> (dist n) ==> (dist n)) array.
  Proof.
    move => ? sl -> tys1 tys2 Htys. constructor => β l; rewrite/ty_own/=. f_equiv.
    elim: Htys l => // ???????? /=. f_equiv. solve_proper.
    by setoid_rewrite offset_loc_S.
  Qed.
  Global Instance array_proper : Proper ((=) ==> (≡) ==> (≡)) array.
  Proof. move => ??->. apply ne_proper, _. Qed.

  Lemma movable_array_forall ly tys `{!MovableLst tys}:
    TCForall (LayoutEq ly) (mty_layout <$> movablelst_to_list tys) →
    Forall (λ ty, ly = (ty : mtype).(ty_layout)) (movablelst_to_list tys).
  Proof. move => /TCForall_Forall. rewrite Forall_fmap => ?. by apply: Forall_impl. Qed.

  Program Definition movable_array ly tys `{!MovableLst tys} `{!TCForall (LayoutEq ly) (mty_layout <$> movablelst_to_list tys)} `{LayoutWf ly}: Movable (array ly tys) := {|
    ty_layout := mk_array_layout ly (length tys);
    ty_own_val v :=
      (⌜v `has_layout_val` (mk_array_layout ly (length tys))⌝ ∗
       [∗ list] v';ty∈reshape (replicate (length tys) (ly_size ly)) v;(movablelst_to_list tys), (v' ◁ᵥ (ty : mtype)))%I;
  |}.
  Next Obligation. by iIntros (ly tys ? Hall%movable_array_forall ? l) "[% Ha]". Qed.
  Next Obligation. by iIntros (ly tys ? ? ? v) "(?&_)". Qed.
  Next Obligation.
    rewrite /LayoutWf. move => ly tys ? /movable_array_forall. rewrite {2}(to_movablelst tys).
    move Heq: (movablelst_to_list tys) => tys'.
    have ->: (length tys = length tys') by rewrite -Heq movablelst_to_list_length.
    clear dependent tys. rewrite /ty_own/=. iIntros (Hlys Hly l) "[_ Htys]".
    iInduction (tys') as [|ty tys] "IH" forall (l); csimpl.
    { iExists []. iSplitR => //. by iApply heap_mapsto_nil. iSplit => //. iPureIntro. rewrite /has_layout_val/ly_size/=. lia. }
    move: Hlys. intros (->&?)%Forall_cons. csimpl.
    rewrite offset_loc_0. iDestruct "Htys" as "[Hty Htys]".
    iDestruct (ty_deref with "Hty") as (v') "[Hl Hty]".
    iDestruct (ty_size_eq with "Hty") as %Hszv.
    setoid_rewrite offset_loc_S.
    iDestruct ("IH" $! _ (l offset{ty_layout ty}ₗ 1) with "Htys") as (vs') "(Hl' & Hsz & Htys)".
    iDestruct "Hsz" as %Hsz. iExists (v' ++ vs').
    rewrite /has_layout_val heap_mapsto_app Hszv offset_loc_1 take_app_alt // drop_app_alt // app_length Hszv Hsz. iFrame.
    iPureIntro. rewrite /ly_size/= -/(ly_size _). lia.
    Unshelve. done.
  Qed.
  Next Obligation.
    rewrite /LayoutWf. move => ly tys ? /movable_array_forall. rewrite {6}(to_movablelst tys).
    move Heq: (movablelst_to_list tys) => tys'.
    have ->: (length tys = length tys') by rewrite -Heq movablelst_to_list_length.
    clear dependent tys. iIntros (Hlys Hly l v Hl) "Hl". rewrite /ty_own/=.
    iDestruct 1 as (Hv) "Htys". iSplit => //.
    iInduction (tys') as [|ty tys] "IH" forall (l v Hv Hl); csimpl in * => //.
    move: Hlys. intros [-> ?]%Forall_cons. iDestruct "Htys" as "[Hty Htys]".
    rewrite -{1}(take_drop (ly_size (ty_layout ty)) v).
    rewrite offset_loc_0 heap_mapsto_app take_length_le ?Hv; last by repeat unfold ly_size => /=; lia.
    iDestruct "Hl" as "[Hl Hl']".
    iDestruct (ty_ref with "[] Hl Hty") as "$" => //.
    setoid_rewrite offset_loc_S. rewrite offset_loc_1.
    iApply ("IH" with "[//] [] [] Hl' Htys"); iPureIntro.
    - rewrite /has_layout_val drop_length Hv. by repeat unfold ly_size => /=; lia.
    - by apply has_layout_loc_ly_mult_offset.
  Qed.


  Lemma array_get_type (i : nat) ly tys ty l β:
    tys !! i = Some ty →
    l ◁ₗ{β} array ly tys -∗ (l offset{ly}ₗ i) ◁ₗ{β} ty ∗ l ◁ₗ{β} array ly (<[ i := singleton_place (l offset{ly}ₗ i)]>tys).
  Proof.
    rewrite !/(ty_own (array _ _))/=. iIntros (Hi) "[$ Ha]".
    iInduction (i) as [|i] "IH" forall (l tys Hi); destruct tys as [|ty' tys] => //; simpl in *; simplify_eq;
      iDestruct "Ha" as "[$ Ha]". by iSplitR.
    rewrite offset_loc_S. setoid_rewrite offset_loc_S.
    iApply ("IH" with "[//] Ha").
  Qed.

  Lemma array_put_type (i : nat) ly tys ty l β:
    (l offset{ly}ₗ i) ◁ₗ{β} ty -∗ l ◁ₗ{β} array ly tys -∗ l ◁ₗ{β} array ly (<[ i := ty ]>tys).
  Proof.
    rewrite !/(ty_own (array _ _))/=. iIntros "Hl [$ Ha]".
    destruct (decide (i < length tys)%nat) as [Hlt |]. 2: {
      rewrite list_insert_ge => //. lia.
    }
    iInduction (i) as [|i] "IH" forall (l tys Hlt); destruct tys as [|ty' tys] => //; simpl in *; simplify_eq.
    - iFrame. by iDestruct "Ha" as "[_ $]".
    - rewrite offset_loc_S. setoid_rewrite offset_loc_S.
      iDestruct "Ha" as "[$ Ha]".
      iApply ("IH" with "[] Hl Ha"). iPureIntro. lia.
  Qed.

  Lemma array_replicate_uninit_equiv l β ly n:
    layout_wf ly →
    l ◁ₗ{β} array ly (replicate n (uninit ly)) ⊣⊢ l ◁ₗ{β} uninit (mk_array_layout ly n).
  Proof.
    rewrite /ty_own/= => ?. iSplit.
    - rewrite heap_mapsto_own_state_layout_alt. iDestruct 1 as (Hl) "Ha". iSplit => //. clear Hl.
      iInduction n as [|n] "IH" forall (l) => /=.
      { iExists []. rewrite heap_mapsto_own_state_nil. iPureIntro. rewrite /has_layout_val/ly_size/=. lia. }
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      iDestruct "Ha" as "[Hl Ha]". iDestruct ("IH" with "Ha") as (v2 Hv2) "Hv2".
      iDestruct "Hl" as (v1 Hv1  Hl1) "Hv1".
      iExists (v1 ++ v2). rewrite heap_mapsto_own_state_app Hv1 /has_layout_val app_length Hv1 Hv2. iFrame.
      iPureIntro. rewrite {2 3}/ly_size/=. lia.
    - iDestruct 1 as (v Hv Hl) "Hl". iSplit => //.
      iInduction n as [|n] "IH" forall (v l Hv Hl) => //=.
      setoid_rewrite offset_loc_S. setoid_rewrite offset_loc_1. rewrite offset_loc_0.
      rewrite -(take_drop (ly.(ly_size)) v) heap_mapsto_own_state_app.
      iDestruct "Hl" as "[Hl Hr]". rewrite take_length_le ?Hv; last by repeat unfold ly_size => /=; lia.
      iSplitL "Hl".
      + iExists _. iFrame. iPureIntro. split => //. rewrite /has_layout_val take_length_le ?Hv; repeat unfold ly_size => /=; lia.
      + iApply ("IH" with "[] [] Hr"); iPureIntro. 2: by apply has_layout_loc_ly_mult_offset.
        rewrite /has_layout_val drop_length Hv; repeat unfold ly_size => /=; lia.
  Qed.

  Lemma simplify_hyp_uninit_array ly l β T n:
    (⌜layout_wf ly⌝ ∗ (l ◁ₗ{β} array ly (replicate n (uninit ly)) -∗ T)) -∗
    simplify_hyp (l ◁ₗ{β} uninit (mk_array_layout ly n)) T.
  Proof. iIntros "[% HT] Hl". iApply "HT". rewrite array_replicate_uninit_equiv // {1}/ly_size/=. Qed.
  Global Instance simplify_hyp_uninit_array_inst ly l β n:
    SimplifyHyp (l ◁ₗ{β} uninit (mk_array_layout ly n)) (Some 0%N) :=
    λ T, i2p (simplify_hyp_uninit_array ly l β T n).

  Lemma subsume_uninit_array_replicate l β T n (ly1 : layout) ly2:
    ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T -∗
    subsume (l ◁ₗ{β} uninit ly1) (l ◁ₗ{β} array ly2 (replicate n (uninit ly2))) T.
  Proof. iIntros "(%&->&$) ?". by rewrite array_replicate_uninit_equiv. Qed.
  Global Instance subsume_uninit_array_replicate_inst l β n ly1 ly2:
    SubsumePlace l β (uninit ly1) (array ly2 (replicate n (uninit ly2))) :=
    λ T, i2p (subsume_uninit_array_replicate l β T n ly1 ly2).

  Lemma subsume_array_replicate_uninit l β T n (ly1 : layout) ly2:
    ⌜layout_wf ly2⌝ ∗ ⌜ly1 = mk_array_layout ly2 n⌝ ∗ T -∗
    subsume (l ◁ₗ{β} array ly2 (replicate n (uninit ly2))) (l ◁ₗ{β} uninit ly1)  T.
  Proof. iIntros "(%&->&$) ?". by rewrite array_replicate_uninit_equiv. Qed.
  Global Instance subsume_array_replicate_uninit_inst l β n ly1 ly2:
    SubsumePlace l β (array ly2 (replicate n (uninit ly2))) (uninit ly1) :=
    λ T, i2p (subsume_array_replicate_uninit l β T n ly1 ly2).

  Lemma subsume_array ly1 ly2 tys1 tys2 l β T:
    ⌜ly1 = ly2⌝ ∗ ⌜length tys1 = length tys2⌝ ∗
    subsume_list type tys1 tys2 (λ i ty, (l offset{ly1}ₗ i) ◁ₗ{β} ty) T -∗
      subsume (l ◁ₗ{β} array ly1 tys1) (l ◁ₗ{β} array ly2 tys2) T.
  Proof.
    iIntros "[-> [Hlen H]] [$ H1]". iDestruct "Hlen" as %Hlen.
    iDestruct ("H" $! Hlen) as "H2".
    iAssert (([^bi_sep list] i↦x ∈ tys2, (l offset{ly2}ₗ i) ◁ₗ{β} x) ∗ T)%I with "[H1 H2]" as "[$ $]".
    by iApply "H2".
  Qed.
  Global Instance subsume_array_inst ly1 ly2 tys1 tys2 l β:
    SubsumePlace l β (array ly1 tys1) (array ly2 tys2) | 100 :=
    λ T, i2p (subsume_array ly1 ly2 tys1 tys2 l β T).

  Lemma subsume_array_insert ly (i : nat) ty tys1 tys2 l β T:
    (∃ ty', ⌜i < length tys1⌝%nat ∗ ⌜<[i := ty']>tys1 = tys2⌝ ∗
       subsume ((l offset{ly}ₗ i) ◁ₗ{β} ty) ((l offset{ly}ₗ i) ◁ₗ{β} ty') T) -∗
    subsume (l ◁ₗ{β} array ly (<[i := ty]>tys1)) (l ◁ₗ{β} array ly tys2) T.
  Proof.
    iDestruct 1 as (ty' Hlen <-) "Hsub". iIntros "Ha".
    iDestruct (array_get_type i with "Ha") as "[H1 Ha]". by apply list_lookup_insert.
    iDestruct ("Hsub" with "H1") as "[H1 HT]".
    iDestruct (array_put_type i with "H1 Ha") as "Ha".
    iApply (subsume_array with "[HT] Ha"). iFrame "HT".
    rewrite !list_insert_insert. repeat iSplit => //. by iIntros "_ $".
  Qed.
  Global Instance subsume_array_insert_inst ly (i : nat) ty tys1 tys2 l β:
    SubsumePlace l β (array ly (<[i := ty]>tys1)) (array ly tys2) | 10:=
    λ T, i2p (subsume_array_insert ly i ty tys1 tys2 l β T).


  Lemma type_place_array l β T ly1 it v (tyv : mtype) tys ly2 K:
    (∃ i', ⌜ly1 = ly2⌝ ∗ subsume (v ◁ᵥ tyv) (v ◁ᵥ i' @ int it) (∃ i : nat, ⌜i' = i⌝ ∗ ⌜i < length tys⌝%nat ∗
     ∀ ty, ⌜tys !! i = Some ty⌝ -∗
    typed_place K (l offset{ly2}ₗ i) β ty (λ l2 β2 ty2 typ, T l2 β2 ty2 (λ t, array ly2 (<[i := typ t]>tys))))) -∗
    typed_place (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array ly2 tys) T.
  Proof.
    iDestruct 1 as (i' ->) "HP". iIntros (Φ) "[% Hl] HΦ" => /=. iIntros "Hv".
    iDestruct ("HP" with "Hv") as "[Hv HP]".
    iDestruct "HP" as (i -> [ty ?]%lookup_lt_is_Some_2) "HP".
    iDestruct (int_val_to_int_Some with "Hv") as %?.
    iApply wp_ptr_offset => //. by apply val_to_of_loc. lia.
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hl Hc]" => //.
    iApply ("HP" $! ty with "[//] Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". iSplitR => //. by iApply "Hc".
  Qed.
  Global Instance type_place_array_inst l β ly1 it v (tyv : mtype) tys ly2 K:
    TypedPlace (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array ly2 tys):=
    λ T, i2p (type_place_array l β T ly1 it v tyv tys ly2 K).

  (*** array iterator *)
  Program Definition array_iterator (ly : layout) (i : nat) (len : nat) (tys1 : list type) (ty : type) (tys2 : list type) : type := {|
    ty_own β l := ⌜i ≤ len⌝%nat ∗ ⌜length tys1 = i⌝ ∗ ⌜length tys2 = (len - i)%nat⌝ ∗ l ◁ₗ{β} array ly (<[i := ty]> (tys1 ++ tys2))
  |}%I.
  Next Obligation. iIntros (?????????). iDestruct 1 as (???) "Ha". do 3 iSplitR => //. by iApply ty_share. Qed.

  Lemma simplify_goal_array_iterator_0 l β T ly len tys1 tys2 ty:
    T (⌜tys1 = []⌝ ∗ ⌜length tys2 = len⌝ ∗ ⌜(0 < len)%nat → tys2 !! 0%nat = Some ty⌝ ∗ l ◁ₗ{β} array ly tys2) -∗
      simplify_goal (l◁ₗ{β} array_iterator ly 0%nat len tys1 ty tys2) T.
  Proof.
    iIntros "HT". iExists _. iFrame. iIntros "[-> [<- [% [$ Ha]]]]".
    repeat iSplit; try iPureIntro => //. lia. by rewrite -minus_n_O.
    rewrite /= list_insert_id'; eauto.
  Qed.
  Global Instance simplify_goal_array_iterator_0_inst l β ly len tys1 tys2 ty:
    SimplifyGoalPlace l β (array_iterator ly 0%nat len tys1 ty tys2)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_array_iterator_0 l β T ly len tys1 tys2 ty).

  Lemma type_place_array_iterator l β T ly1 it v (tyv : mtype) (i : nat) len tys1 ty tys2 ly2 K:
    ⌜i < len⌝%nat ∗ ⌜ly1 = ly2⌝ ∗ subsume (v ◁ᵥ tyv) (v ◁ᵥ i @ int it) (
    typed_place K (l offset{ly2}ₗ i) β ty (λ l2 β2 ty2 typ, T l2 β2 ty2 (λ t, array_iterator ly2 i len tys1 (typ t) tys2))) -∗
    typed_place (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array_iterator ly2 i len tys1 ty tys2) T.
  Proof.
    iIntros "[% [<- HP]]" (Φ) "[% [<- [% [% Hl]]]] HΦ" => /=. iIntros "Hv".
    (* TODO: this is the same as type_place_array. Figure out if we can reuse the proof. *)
    iDestruct ("HP" with "Hv") as "[Hv HP]".
    iDestruct (int_val_to_int_Some with "Hv") as %?.
    iApply wp_ptr_offset => //. by apply val_to_of_loc. lia.
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hl") as "[Hl Hc]" => //.
      by apply list_lookup_insert; rewrite app_length; lia.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". repeat  iSplitR => //.
    setoid_rewrite list_insert_insert. by iApply ("Hc").
  Qed.
  Global Instance type_place_array_iterator_inst l β ly1 it v (tyv : mtype) (i : nat) len tys1 ty tys2 ly2 K:
    TypedPlace (BinOpPCtx (PtrOffsetOp ly1) (IntOp it) v tyv :: K) l β (array_iterator ly2 i len tys1 ty tys2) :=
    λ T, i2p (type_place_array_iterator l β T ly1 it v tyv i len tys1 ty tys2 ly2 K).

  Lemma subsume_array_iterator_next l β T i1 i2 len ly tys11 ty1 tys21 tys12 ty2 tys22 `{!CanSolve (i2 = S i1)}:
    (∃ ty1', ⌜tys12 = tys11 ++ [ty1']⌝ ∗ ⌜length tys21 > 0⌝%nat ∗ ⌜tail tys21 = tys22⌝ ∗
         ⌜(i2 < len)%nat → tys22 !! 0%nat = Some ty2⌝ ∗
        subsume ((l offset{ly}ₗ i1) ◁ₗ{β} ty1) ((l offset{ly}ₗ i1) ◁ₗ{β} ty1') T) -∗
    subsume (l ◁ₗ{β} array_iterator ly i1 len tys11 ty1 tys21) (l ◁ₗ{β} array_iterator ly i2 len tys12 ty2 tys22) T.
  Proof.
    unfold CanSolve in *; subst.
    iDestruct 1 as (ty1' -> Htys21 <- Hty2) "Hsub". destruct tys21 as [|ty' tys21]; simpl in *. lia.
    iDestruct 1 as (? <- Hlen) "Ha". rewrite insert_app_r_alt // -minus_n_n/=.
    iDestruct (array_get_type (length tys11) with "Ha") as "[Hty1 Ha]". by rewrite lookup_app_r // -minus_n_n //.
    iDestruct ("Hsub" with "Hty1") as "[Hty1 $]".
    iSplit; [|iSplit]; [..|iSplit]; try iPureIntro; simpl in *. lia. by rewrite app_length /=; lia. lia.
    iDestruct (array_put_type with "Hty1 Ha") as "Ha".
    rewrite list_insert_insert insert_app_r_alt // insert_app_r_alt ?app_length /=; last lia.
    rewrite  -minus_n_n/=. have -> : (S (length tys11) - (length tys11 + 1) = 0)%nat by lia.
    destruct tys21 as [|ty'' tys21] => /=. by rewrite app_nil_r.
    simpl in *. rewrite -app_assoc cons_middle.
    by have [->]: Some ty'' = Some ty2 by eauto with lia.
  Qed.
  Global Instance subsume_array_iterator_next_inst l β i1 i2 len ly tys11 ty1 tys21 tys12 ty2 tys22 `{!CanSolve (i2 = S i1)}:
    SubsumePlace l β (array_iterator ly i1 len tys11 ty1 tys21) (array_iterator ly i2 len tys12 ty2 tys22) :=
    λ T, i2p (subsume_array_iterator_next l β T i1 i2 len ly tys11 ty1 tys21 tys12 ty2 tys22).

  (* TODO: support not iterating until the end? *)
  Lemma subsume_array_iterator_array l β T i len ly tys1 ty tys2 tys':
    ⌜len ≤ i⌝%nat ∗ ⌜tys1 = tys'⌝ ∗ (⌜i = len⌝ -∗ T) -∗
    subsume (l ◁ₗ{β} array_iterator ly i len tys1 ty tys2) (l ◁ₗ{β} array ly tys') T.
  Proof.
    iIntros "(%&->&HT)".
    iDestruct 1 as (? <- Hlen) "Ha". iDestruct ("HT" with "[]") as "$". by iPureIntro; lia.
    rewrite insert_app_r_alt // -minus_n_n/=.
    destruct tys2; simpl in *. by rewrite app_nil_r. lia.
  Qed.
  Global Instance subsume_array_iterator_array_inst l β i len ly tys1 ty tys2 tys':
    SubsumePlace l β (array_iterator ly i len tys1 ty tys2) (array ly tys') :=
    λ T, i2p (subsume_array_iterator_array l β T i len ly tys1 ty tys2 tys').
End type.
