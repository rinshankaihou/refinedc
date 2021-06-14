From refinedc.typing Require Export type.
From iris.algebra Require Import list.
From refinedc.typing Require Import programs bytes.
Set Default Proof Using "Type".

Section struct.
  Context `{!typeG Σ}.

  (* We cannot only allow mtypes in structs as we want to be able to
   borrow from fields.

   Should we have a later in here to avoid the use of guarded in most
   cases? Probably not because subtyping would break (later in the
   goal would be only around the struct, not the whole goal. ). *)
  Program Definition struct (sl : struct_layout) (tys : list type) : type := {|
    ty_own β l :=
      ⌜l `has_layout_loc` sl⌝ ∗ ⌜length (field_names sl.(sl_members)) = length tys⌝ ∗
      loc_in_bounds l (sum_list (ly_size <$> (sl_members sl).*2)) ∗
      [∗ list] i↦ty∈pad_struct sl.(sl_members) tys uninit,
        (l +ₗ Z.of_nat (offset_of_idx sl.(sl_members) i)) ◁ₗ{β} ty;
  |}%I.
  Next Obligation.
    iIntros (?????) "[% [% [#Hb HP]]]". do 3 iSplitR => //.
    iApply big_sepL_fupd. iApply (big_sepL_impl with "HP").
    iIntros "!#" (???) => /=. by iApply ty_share.
  Qed.


  Global Instance struct_ne n : Proper ((=) ==> (dist n) ==> (dist n)) struct.
  Proof.
    move => ? sl -> tys1 tys2 Htys. constructor => β l; rewrite/ty_own/=/offset_of_idx.
    f_equiv. f_equiv; first by move: Htys => /Forall2_length->. f_equiv.
    elim: (sl_members sl) tys1 tys2 Htys l => // -[m ?] s IH tys1 tys2 Htys l. csimpl.
    f_equiv. solve_proper. setoid_rewrite <-shift_loc_assoc_nat; apply IH => //.
    destruct m, Htys => //. by f_equiv.
  Qed.
  Global Instance struct_proper : Proper ((=) ==> (≡) ==> (≡)) struct.
  Proof. move => ??->. apply ne_proper, _. Qed.

  Lemma struct_focus l β sl tys:
    l ◁ₗ{β} struct sl tys -∗ ([∗ list] n;ty∈field_names sl.(sl_members);tys, l at{sl}ₗ n ◁ₗ{β} ty) ∗ (∀ tys',
           ([∗ list] n;ty∈field_names sl.(sl_members);tys', l at{sl}ₗ n ◁ₗ{β} ty) -∗ l ◁ₗ{β} struct sl tys').
  Proof.
    rewrite {1 4}/ty_own/=. iIntros "[$ Hs]". iDestruct "Hs" as (Hcount) "[#Hb Hs]".
    rewrite /GetMemberLoc/offset_of_idx.
    have HND : (NoDup (field_names (sl_members sl))) by eapply bool_decide_unpack, sl_nodup.
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (l tys Hcount HND). {
      destruct tys => //. iSplit => //. iIntros (tys') "Htys".
      iDestruct (big_sepL2_nil_inv_l with "Htys") as %->. iFrame. by iSplit.
    }
    csimpl. iDestruct "Hs" as "[Hl Hs]".
    iDestruct (loc_in_bounds_split with "Hb") as "[Hb1 Hb2]".
    setoid_rewrite <-shift_loc_assoc_nat.
    iDestruct ("IH" with "[] [] Hb2 Hs") as "[Hl1 Hs]"; try iPureIntro.
    { by destruct n, tys; naive_solver. }
    { destruct n => //. apply: NoDup_cons_1_2. naive_solver. }
    iClear "IH". destruct n; csimpl.
    - destruct tys => //=. rewrite offset_of_cons; eauto. case_decide => //=. iFrame.
      iSplitL "Hl1". {
        iApply (big_sepL2_impl with "Hl1"). iIntros "!#" (k n ty Hm ?) "Hl".
        move: Hm => /(elem_of_list_lookup_2 _ _ _) ?.
        rewrite offset_of_cons; eauto. case_decide; last by rewrite shift_loc_assoc_nat.
        move: HND => /= /(NoDup_cons_1_1 _ _). set_solver.
      }
      iIntros (tys') "Htys".
      iDestruct (big_sepL2_cons_inv_l with "Htys") as (?? ->)"[H1 Htys]".
      rewrite offset_of_cons; eauto. case_decide => //=. iFrame.
      iDestruct (big_sepL2_length with "Htys") as %<-. iSplitR => //.
      iSplit. { iApply loc_in_bounds_split. eauto. }
      iDestruct ("Hs" with "[Htys]") as (?) "[_ $]".
      iApply (big_sepL2_impl with "Htys"). iIntros "!#" (k n ty Hm ?) "Hl".
      move: Hm => /(elem_of_list_lookup_2 _ _ _) ?.
      rewrite offset_of_cons; eauto. case_decide; last by rewrite shift_loc_assoc_nat.
      move: HND => /= /(NoDup_cons_1_1 _ _). set_solver.
    - iFrame. iSplitL "Hl1". {
        iApply (big_sepL2_impl with "Hl1"). iIntros "!#" (k n ty Hm ?) "Hl".
        move: Hm => /(elem_of_list_lookup_2 _ _ _) ?.
        rewrite offset_of_cons; eauto. case_decide => //. by rewrite shift_loc_assoc_nat.
      }
      iIntros (tys') "Htys".
      iDestruct ("Hs" with "[Htys]") as (?) "[_ $]" => //; last by iSplit.
      iApply (big_sepL2_impl with "Htys"). iIntros "!#" (k n ty Hm ?) "Hl".
      move: Hm => /(elem_of_list_lookup_2 _ _ _) ?.
      rewrite offset_of_cons; eauto. case_decide => //. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma movable_struct_forall sl tys `{!MovableLst tys}:
    TCForall2 LayoutEq sl.(sl_members).*2 (pad_struct sl.(sl_members) (mty_layout <$> movablelst_to_list tys) id) →
    Forall2 (λ m ty, m.2 = (ty : mtype).(ty_layout)) sl.(sl_members) (pad_struct sl.(sl_members) (movablelst_to_list tys) (λ ly, t2mt (uninit ly))).
  Proof.
    move => /TCForall2_Forall2. move: (movablelst_to_list tys). clear dependent tys => tys.
    elim: (sl_members sl) tys. by move => ??; constructor.
    move => [[?|]?] ? IH tys; csimpl => /(Forall2_cons_inv _ _ _ _)[Heq ?]; eauto.
    by constructor => /=; destruct tys; inversion Heq; eauto.
  Qed.

  (* MovableLst gets solved to late if we make this an instance (tc
  search first tries to solve TCForall2 which fails since MovableLst
  is still an evar) *)
  Program Definition movable_struct sl tys `{!MovableLst tys} :
    TCForall2 LayoutEq sl.(sl_members).*2 (pad_struct sl.(sl_members) (mty_layout <$> movablelst_to_list tys) id) →
    Movable (struct sl tys) := fun P => {|
    ty_layout := sl;
    ty_own_val v :=
      (⌜v `has_layout_val` sl⌝ ∗ ⌜length (field_names sl.(sl_members)) = length tys⌝ ∗
       [∗ list] v';ty∈reshape (ly_size <$> sl.(sl_members).*2) v;pad_struct sl.(sl_members) (movablelst_to_list tys) (λ ly, t2mt (uninit ly)), (v' ◁ᵥ (ty : mtype)))%I;
  |}.
  Next Obligation. by iIntros (sl tys ? ? l) "(?&_)". Qed.
  Next Obligation. by iIntros (sl tys ? ? v) "(?&_)". Qed.
  Next Obligation.
    move => sl tys ? /movable_struct_forall. rewrite {2 3}(to_movablelst tys).
    move: (movablelst_to_list tys) => tys'. clear dependent tys.
    iIntros (Hlys l) "Htys". iDestruct "Htys" as (_ Hcount) "[#Hb Htys]".
    rewrite /=/layout_of{1}/has_layout_val{1}/ly_size.
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (tys' l Hlys Hcount); csimpl.
    { iExists []. iSplitR; first by iApply heap_mapsto_nil. iSplit => //. }
    move: Hlys => /=. intros (ty & tys & Hsz &?&?)%Forall2_cons_inv_l. move: Hsz; csimpl => ->.
    rewrite shift_loc_0. iDestruct "Htys" as "[Hty Htys]". cbn.
    iDestruct (loc_in_bounds_split with "Hb") as "[Hb1 Hb2]".
    setoid_rewrite <-shift_loc_assoc_nat.
    destruct n => /=.
    1: destruct tys' => //; csimpl.
    all: iDestruct (ty_deref with "Hty") as (v') "[Hl Hty]".
    all: iDestruct (ty_size_eq with "Hty") as %Hszv.
    all: iDestruct ("IH" $! _ with "[] [] Hb2 Htys") as (vs') "(Hl' & Hsz & Hf & Htys)";
      try iPureIntro; simplify_eq => //.
    all: iDestruct "Hsz" as %Hsz; iDestruct "Hf" as %Hf.
    all: iExists (v' ++ vs').
    all: rewrite heap_mapsto_app -Hsz -Hszv take_app drop_app app_length; iFrame.
    all: rewrite Hszv; iFrame "Hl'".
    all: iPureIntro; eauto with lia.
    all: split; last by f_equal.
    all: by rewrite /ly_size /= Hsz.
  Qed.
  Next Obligation.
    move => sl tys ? /movable_struct_forall. rewrite {2 4}(to_movablelst tys).
    move: (movablelst_to_list tys) => tys'. clear dependent tys. iIntros (Hlys l v Hly) "Hl".
    rewrite /layout_of/has_layout_val{1}/ly_size /=.
    iDestruct 1 as (Hv Hcount) "Htys". do 2 iSplitR => //.
    have {}Hly := check_fields_aligned_alt_correct _ _ Hly.
    iSplit. { rewrite -Hv. by iApply heap_mapsto_loc_in_bounds. }
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (tys' l v Hlys Hv Hcount Hly); csimpl in * => //.
    iDestruct "Htys" as "[Hty Htys]".
    move: Hlys. intros [Hsz ?]%Forall2_cons_inv. move: Hly => [??].
    rewrite -(take_drop (ly_size ly) v).
    rewrite shift_loc_0 heap_mapsto_app take_app_alt ?take_length_le // ?Hv; try by cbn; lia.
    iDestruct "Hl" as "[Hl Hl']". cbn.
    setoid_rewrite <-shift_loc_assoc_nat.
    iSplitR "Htys Hl'".
    - iClear "IH".
      destruct n; [destruct tys' => //|] => /=; iDestruct (ty_ref with "[] Hl Hty") as "$" => //. by rewrite -Hsz.
    - destruct n => /=; rewrite -?fmap_tail; iApply ("IH" with "[] [] [] [] Hl' [Htys]") => //;
        iClear "IH"; try iPureIntro; rewrite ?drop_length; try lia.
      all: try by rewrite Hv /struct_size/offset_of_idx; csimpl; lia.
      1: destruct tys'; naive_solver.
      all: rewrite drop_app_alt ?take_length// Hv; cbn; lia.
  Qed.

  Global Instance struct_loc_in_bounds sl tys β : LocInBounds (struct sl tys) β (ly_size sl).
  Proof.
    constructor. by iIntros (l) "(_&_&?&_)".
  Qed.

  Global Instance struct_alloc_alive sl tys β P `{!TCExists (λ ty, AllocAlive ty β P) tys} :
    AllocAlive (struct sl tys) β P.
  Proof.
    revert select (TCExists _ _).
    rewrite TCExists_Exists Exists_exists => -[x [/(elem_of_list_lookup_1 _ _) [i Hx] ?]].
    constructor. iIntros (l) "HP Hl".
    iDestruct (struct_focus with "Hl") as "[Hl _]".
    iDestruct (big_sepL2_length with "Hl") as %Hlen.
    have [|n Hn] := lookup_lt_is_Some_2 (field_names (sl_members sl)) i.
    { rewrite Hlen. by apply: lookup_lt_Some. }
    iDestruct (big_sepL2_lookup with "Hl") as "Hl" => //.
    iDestruct (alloc_alive_alive with "HP Hl") as "Hl".
    by iApply (alloc_alive_loc_mono with "Hl").
  Qed.

  Global Instance strip_guarded_struct sl tys tys' E1 E2 β {Hs :StripGuardedLst β E1 E2 tys tys'}:
    StripGuarded β E1 E2 (struct sl tys) (struct sl tys').
  Proof.
    iIntros (l E  HE1 HE2) "Hs".
    iDestruct (struct_focus with "Hs") as "[Hs Hc]".
    iDestruct (Hs (GetMemberLoc l sl <$> omap fst (sl_members sl))) as "-#Hstrip" => //.
    rewrite !big_sepL2_fmap_l /=. iApply "Hc".
    by iApply "Hstrip".
  Qed.

  Lemma struct_mono sl tys1 tys2 l β T:
    ⌜length tys1 = length tys2⌝ ∗ foldr (λ e T, subsume (l at{sl}ₗ e.2.2 ◁ₗ{β} e.1) (l at{sl}ₗ e.2.2 ◁ₗ{β} e.2.1) T) T (zip tys1 (zip tys2 (field_names sl.(sl_members)))) -∗
    subsume (l ◁ₗ{β} struct sl tys1) (l ◁ₗ{β} struct sl tys2) T.
  Proof.
    iDestruct 1 as (Hlen) "H". iIntros "Hl".
    iDestruct (struct_focus with "Hl") as "[Hs Hc]".
    iSpecialize ("Hc" $! tys2). move: {3 4}(tys2) => tys2'.
    move: (field_names (sl_members sl)) => ns.
    iInduction ns as [|n ns] "IH" forall (l tys1 tys2 Hlen).
    { destruct tys1, tys2 => //. iFrame. by iApply "Hc". }
    iDestruct (big_sepL2_cons_inv_l with "Hs") as (ty1 tys1' ?) "[H1 Hs]"; subst.
    destruct tys2 => //=. iDestruct ("H" with "H1") as "[H1 H]".
    iApply ("IH" with "[] H Hs"). naive_solver.
    iIntros "H". iApply "Hc". by iFrame.
  Qed.
  Global Instance struct_mono_inst sl tys1 tys2 l β:
    SubsumePlace l β (struct sl tys1) (struct sl tys2) | 10 :=
    λ T, i2p (struct_mono sl tys1 tys2 l β T).

  Lemma type_place_struct K β1 T tys tys' sl n l E1 E2 `{!DoStripGuarded β1 E1 E2 (struct sl tys) (struct sl tys')}:
    (∃ i ty1, ⌜field_index_of sl.(sl_members) n = Some i⌝ ∗
    ⌜tys' !! i = Some ty1⌝ ∗
    typed_place K (l at{sl}ₗ n) β1 ty1 (λ l2 β ty2 typ, T l2 β ty2 (λ t, struct sl (<[i := (typ t)]> tys')))) -∗
    typed_place (GetMemberPCtx sl n :: K) l β1 (struct sl tys) T.
  Proof.
    iDestruct 1 as (i ty1 Hi Hn) "HP".
    move: (Hi) => /field_index_of_to_index_of[? Hi2].
    iIntros (Φ) "Hs HΦ" => /=.
    iDestruct (loc_in_bounds_in_bounds with "Hs") as "#Hlib".
    iApply (wp_step_fupd with "[Hs]"). done. 2: by iApply (do_strip_guarded with "Hs"). solve_ndisj.
    iApply wp_get_member. by apply val_to_of_loc. by eauto. done.
    iIntros "!# [% [% [#Hb Hs]]] !#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hs") as "[Hl Hs]" => //=. by eapply pad_struct_lookup_field.
    rewrite /GetMemberLoc/offset_of Hi2/=.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Hc HT".
    iApply ("HΦ" with "Hl' [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iDestruct ("Hs" with "Hty") as "Hs". iSplitR => //. iSplitR; first by rewrite insert_length.
    iFrame "Hb". erewrite pad_struct_insert_field => //. have := field_index_of_leq _ _ _ Hi. lia.
  Qed.
  Global Instance type_place_struct_inst K β1 tys tys' sl n l E1 E2 `{!DoStripGuarded β1 E1 E2 (struct sl tys) (struct sl tys')} :
    TypedPlace (GetMemberPCtx sl n :: K) l β1 (struct sl tys) | 10 :=
    λ T, i2p (type_place_struct K β1 T tys tys' sl n l E1 E2).

  (* Ail fills in the missing elements in fs, so we can assume that
  the lookup will always succeed. This is nice, because otherwise we
  would get a quadractic blowup when simiplifying the foldr. *)
  Lemma type_struct_init sl fs T:
    foldr (λ n f, (λ tys, ∃ e : expr, ⌜(list_to_map fs : gmap _ _) !! n = Some e⌝ ∗
      typed_val_expr e (λ _ ty, f (tys ++ [ty]))))
    (λ tys : list mtype, ∀ v, let Hlst := list_to_movablelst tys in
      ∃ (Hall : TCForall2 LayoutEq sl.(sl_members).*2 (pad_struct sl.(sl_members) (mty_layout <$> movablelst_to_list (mt_type <$> tys)) id)),
        T v (@t2mt _ _ (struct sl (mt_type <$> tys)) (movable_struct _ _ _))) (omap fst sl.(sl_members)) [] -∗
    typed_val_expr (StructInit sl fs) T.
  Proof.
    iIntros "He" (Φ) "HΦ". iApply wp_struct_init.
    iAssert ([∗ list] v';ty∈[];pad_struct ([@{option var_name * layout}]) [] (λ ly, t2mt (uninit ly)), (v' ◁ᵥ (ty : mtype)))%I as "-#Hvs". done.
    have : [] ++ sl.(sl_members) = sl.(sl_members) by simplify_list_eq.
    have : [] = reshape (ly_size <$> (pad_struct [] (mty_layout <$> []) id)) [@{mbyte}] by [].
    have : length (@nil mbyte) = sum_list (ly_size <$> (pad_struct [] (mty_layout <$> []) id)) by [].
    have : length (field_names []) = length [@{mtype}] by [].
    move: {1 2 3 5 6}(@nil mtype) => tys.
    move: {1 2 4}(@nil val) => vs.
    move: {1 2}(@nil (mbyte)) => v.
    move: {1 2 3 4 5}(@nil (option var_name * layout)) => s.
    move: {1 7 8}(sl_members sl) => slm Hf Hv Hvs Hs.
    iInduction (slm) as [|[n ?] ms] "IH" forall (vs tys v s Hs Hvs Hv Hf); csimpl.
    - iDestruct ("He" $! (mjoin vs)) as (Hall) "HT". iApply ("HΦ" with "[-HT] HT"). simplify_list_eq.
      move: (Hall) => Hall1. move: Hall => /movable_struct_forall Hall2. rewrite of_movablelst in Hall2.
      rewrite {2}/ty_own_val/=/layout_of{3}/ly_size of_movablelst. clear Hall1.
      rewrite join_reshape // ?fmap_length//.
      have -> : ((sl_members sl).*2 = pad_struct (sl_members sl) (mty_layout <$> tys) id). {
        clear Hf Hv.
        elim: (sl_members sl) tys Hall2 => // -[[?|] ?]; csimpl => ? IH tys => /(Forall2_cons_inv _ _ _ _)/=[Heq Hf];
          rewrite (IH _ Hf) // Heq.
        by destruct tys.
      }
      by iFrame.
    - rewrite cons_middle assoc in Hs. destruct n => /=.
      + iDestruct "He" as (e ->) "He". iApply "He". iIntros (v1 ty) "Hv Hf".
        iDestruct (ty_size_eq with "Hv") as %Hsz.
        iApply ("IH" $! _ _ (v ++ v1) with "[//] [] [] [] Hf HΦ");
          try iPureIntro; rewrite ?fmap_app ?pad_struct_snoc_Some ?fmap_length //.
        * by rewrite fmap_app reshape_app take_app_alt ?drop_app_alt /= ?take_ge ?Hsz; subst.
        * by rewrite app_length fmap_app sum_list_with_app /= Hsz -Hv /mty_layout; lia.
        * by rewrite /field_names omap_app !app_length Hf.
        * iApply (big_sepL2_app with "Hvs"). by iFrame.
      + iApply @wp_value.
        iApply ("IH" $! _ _ (v ++ replicate (ly_size l) ☠%V) with "[//] [] [] [] He HΦ");
          try iPureIntro; rewrite ?fmap_app ?pad_struct_snoc_None.
        * by rewrite fmap_app reshape_app take_app_alt ?drop_app_alt /= ?take_ge ?Hsz ?replicate_length; subst.
        * rewrite app_length fmap_app sum_list_with_app Hv replicate_length /=. lia.
        * by rewrite /field_names omap_app !app_length Hf.
        * iApply (big_sepL2_app with "Hvs"). iSplit => //. iPureIntro.
          split; first by rewrite /has_layout_val replicate_length.
          by apply Forall_forall.
  Qed.


  Lemma uninit_struct_equiv l β (s : struct_layout) :
    (l ◁ₗ{β} uninit s) ⊣⊢ (l ◁ₗ{β} struct s (uninit <$> omap (λ '(n, ly), const ly <$> n) s.(sl_members))).
  Proof.
    rewrite /layout_of/struct{1 2}/ty_own/offset_of_idx/=.
    iSplit.
    - iDestruct 1 as (v Hv Hl _) "Hl". iSplit => //. iSplit.
      { iPureIntro. rewrite fmap_length. by apply omap_length_eq => i [[?|]?]. }
      have {}Hl := check_fields_aligned_alt_correct _ _ Hl.
      rewrite /has_layout_val{1}/ly_size in Hv.
      iSplit. { iApply loc_in_bounds_shorten; last by iApply heap_mapsto_own_state_loc_in_bounds. lia. }
      iInduction (sl_members s) as [|[n ly] ms] "IH" forall (v l Hl Hv) => //; csimpl in *.
      rewrite shift_loc_0. setoid_rewrite <-shift_loc_assoc_nat. move: Hl => [??].
      have Hlen: (length (take (ly_size ly) v) = ly_size ly) by rewrite take_length_le ?Hv//; cbn; lia.
      rewrite -(take_drop ly.(ly_size) v).
      iDestruct (heap_mapsto_own_state_app with "Hl") as "[Hl Hr]". rewrite Hlen.
      iSplitL "Hl"; destruct n; try by [iExists _; iFrame; rewrite Forall_forall]; iApply "IH" => //;
      try rewrite drop_length; try iPureIntro; lia.
    - iIntros "[$ Hl]". iDestruct "Hl" as (_) "[#Hb Hl]".
      rewrite /has_layout_val{2}/ly_size.
      iInduction (sl_members s) as [|[n ly] ms] "IH" forall (l) => //; csimpl in *.
      { iExists []. rewrite Forall_nil. repeat iSplit => //. by rewrite heap_mapsto_own_state_nil. }
      rewrite shift_loc_0. setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct "Hl" as "[Hl Hs]".
      iDestruct (loc_in_bounds_split with "Hb") as "[Hb1 Hb2]".
      destruct n; csimpl.
      all: rewrite /ty_own/=; iDestruct "Hl" as (v1 Hv1 Hl _) "Hl".
      all: iDestruct ("IH" with "Hb2 Hs") as (v2 Hv2 _) "Hv".
      all: iExists (v1 ++ v2).
      all: rewrite heap_mapsto_own_state_app app_length Hv1 Hv2.
      all: rewrite Forall_app !Forall_forall.
      all: by iFrame.
  Qed.

  Lemma uninit_struct_simpl_hyp l β (s : struct_layout) T:
    (l ◁ₗ{β} (struct s (uninit <$> omap (λ '(n, ly), const ly <$> n) s.(sl_members))) -∗ T) -∗
    simplify_hyp (l ◁ₗ{β} uninit s) T.
  Proof. iIntros "HT Hl". rewrite uninit_struct_equiv. by iApply "HT". Qed.
  Global Instance uninit_struct_simpl_hyp_inst l β (s : struct_layout):
    SimplifyHypPlace l β (uninit s) (Some 0%N) :=
    λ T, i2p (uninit_struct_simpl_hyp l β s T).

  Lemma uninit_struct_simpl_goal l β (s : struct_layout) T:
    T (l ◁ₗ{β} (struct s (uninit <$> omap (λ '(n, ly), const ly <$> n) s.(sl_members)))) -∗
    simplify_goal (l ◁ₗ{β} uninit s) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "?". by rewrite uninit_struct_equiv. Qed.
  Global Instance uninit_struct_simpl_goal_inst l β (s : struct_layout):
    SimplifyGoalPlace l β (uninit s) (Some 50%N) :=
    λ T, i2p (uninit_struct_simpl_goal l β s T).
End struct.

Hint Extern 1 (Movable (struct ?s ?tys)) => simple apply (movable_struct s tys) : typeclass_instances.
Typeclasses Opaque struct.
