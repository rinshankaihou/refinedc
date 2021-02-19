From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes padded int struct.
Set Default Proof Using "Type".

Section function.
  Context `{!typeG Σ}.

  (*** active_union *)
  Program Definition active_union (ul : union_layout) (f : var_name) (ty : type) : type := {|
    ty_own β l := (∃ ly, ⌜layout_of_union_member f ul = Some ly⌝ ∗ l ◁ₗ{β} (padded ty ly ul))%I
  |}.
  Next Obligation.
    iIntros (ul f ty l E ?). iDestruct 1 as (ly ?) "Hp". iExists _. iSplitR => //. by iApply ty_share.
  Qed.

  Lemma type_place_uninit_union K β T ul n l:
    (∃ ly, ⌜layout_of_union_member n ul = Some ly⌝ ∗
    typed_place (GetMemberUnionPCtx ul n :: K) l β (active_union ul n (uninit ly)) T) -∗
    typed_place (GetMemberUnionPCtx ul n :: K) l β (uninit ul) T.
  Proof.
    iDestruct 1 as (ly Hly) "HP".
    iIntros (Φ) "Hs HΦ" => /=.
    iApply ("HP" with "[Hs] HΦ").
    iExists _. iSplit => //.
    iApply (apply_subsume_place_true with "Hs"). iApply subsume_uninit_padded.
    iSplit => //. iPureIntro.
    split; apply max_list_elem_of_le; apply elem_of_list_fmap_1; by apply: layout_of_union_member_in_ul.
  Qed.
  Global Instance type_place_uninit_union_inst K β ul n l :
    TypedPlace (GetMemberUnionPCtx ul n :: K) l β (uninit ul) :=
    λ T, i2p (type_place_uninit_union K β T ul n l).

  Lemma type_place_active_union K β T ul n l ty:
    typed_place K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, active_union ul n (typ t))) -∗
    typed_place (GetMemberUnionPCtx ul n :: K) l β (active_union ul n ty) T.
  Proof.
    iIntros "HP" (Φ) "Hs HΦ" => /=.
    iDestruct "Hs" as (ly ?) "Hpad".
    rewrite /padded. iDestruct "Hpad" as (??) "[Hb [Hty Hpad]]".
    iApply wp_get_member_union. by apply val_to_of_loc. iExists _. iSplit => //.
    iApply ("HP" with "[Hty]"). by rewrite /GetMemberUnionLoc.
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iExists _. iSplitR => //. rewrite /padded/GetMemberUnionLoc. by iFrame.
  Qed.
  Global Instance type_place_active_union_inst K β ul n l ty :
    TypedPlace (GetMemberUnionPCtx ul n :: K) l β (active_union ul n ty) :=
    λ T, i2p (type_place_active_union K β T ul n l ty).

  (*** tagged union *)
  (*** tunion_info *)
  Record tunion_info := {
    ti_rtype : Type;
    ti_base_layout : struct_layout;
    ti_tag_field_name : string;
    ti_union_field_name : string;
    ti_union_layout : union_layout;
    ti_tag : ti_rtype → nat;
    ti_type : ti_rtype → type;

    ti_base_layout_members : ti_base_layout.(sl_members) = [(Some ti_tag_field_name, it_layout size_t); (Some ti_union_field_name, ul_layout ti_union_layout)];
    ti_tags_valid r : is_Some (ti_union_layout.(ul_members) !! ti_tag r);
  }.

  Definition ti_member (ti : tunion_info) (r : ti.(ti_rtype)) :=
    (default ("", void_layout) (ti.(ti_union_layout).(ul_members) !! ti.(ti_tag) r)).

  Lemma index_of_ti_member ti x:
    index_of_union (ti_member ti x).1 (ti_union_layout ti) = Some (ti.(ti_tag) x).
  Proof.
    rewrite /ti_member.
    destruct (ti_tags_valid ti x) as [[n ly] Heq]. rewrite Heq /=.
    by apply: index_of_union_lookup.
  Qed.

  Lemma layout_of_member_ti_member ti x ly:
    layout_of_union_member (ti_member ti x).1 (ti_union_layout ti) = Some ly →
    ly = (ti_member ti x).2.
  Proof.
    rewrite /layout_of_union_member index_of_ti_member/=/ti_member.
    by destruct (ul_members (ti_union_layout ti) !! ti_tag ti x) => //= [[]].
  Qed.

  (*** tag *)
  Program Definition tunion_tag (ti : tunion_info) (x : ti.(ti_rtype)) : type := {|
    ty_own β l := l ◁ₗ{β}ti.(ti_tag) x @ int size_t
  |}%I.
  Next Obligation. iIntros (?????). by iApply ty_share. Qed.

  Global Program Instance movable_tunion_tag ti x : Movable (tunion_tag ti x) := {|
    ty_layout := size_t;
    ty_own_val v := v ◁ᵥ ti.(ti_tag) x @ int size_t;
  |}%I.
  Next Obligation. iIntros (???) "Hl". rewrite /ty_own/=. by iDestruct (ty_aligned with "Hl") as %?. Qed.
  Next Obligation. iIntros (???) "Hv". by iDestruct (ty_size_eq with "Hv") as %?. Qed.
  Next Obligation. iIntros (???) => /=. rewrite /ty_own/=. by apply ty_deref. Qed.
  Next Obligation. iIntros (?????) "Hl Hv" => /=. rewrite /ty_own/=. by iApply (ty_ref with "[] Hl Hv"). Qed.

  Global Program Instance copyable_tunion_tag ti x : Copyable (tunion_tag ti x).
  Next Obligation.
    rewrite /ty_own/ty_own_val/= => ?????/=.
    iIntros "Hl". iMod (copy_shr_acc with "Hl") as (???) "Hc" => //. iSplitR => //. iExists _, _. by iFrame.
  Qed.

  Lemma subsume_int_tunion_tag ti x (n : Z) l β T:
    ⌜ti.(ti_tag) x =@{Z} n⌝ ∗ T -∗
    subsume (l ◁ₗ{β} n @ int size_t) (l ◁ₗ{β} tunion_tag ti x) T.
  Proof. iIntros "[<- $] ?". by rewrite /tunion_tag/=. Qed.
  Global Instance subsume_int_tunion_tag_inst ti x (n : Z) l β:
    SubsumePlace l β (n @ int size_t)%I (tunion_tag ti x) :=
    λ T, i2p (subsume_int_tunion_tag ti x n l β T).

  Lemma subsume_tunion_tag ti x1 x2 l β T:
    ⌜ti.(ti_tag) x1 = ti.(ti_tag) x2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} tunion_tag ti x1) (l ◁ₗ{β} tunion_tag ti x2) T.
  Proof. rewrite /ty_own/=. iIntros "[-> $] $". Qed.
  Global Instance subsume_tunion_tag_inst ti x1 x2 l β:
    SubsumePlace l β (tunion_tag ti x1)%I (tunion_tag ti x2) :=
    λ T, i2p (subsume_tunion_tag ti x1 x2 l β T).

  Inductive destruct_hint_union :=
  | DestructHintUnion (info : tunion_info).

  Lemma type_binop_tunion_tag_int ti x it v1 n v2 T op:
    destruct_hint (DHintDestruct _ x) (DestructHintUnion ti) (typed_bin_op v1 (v1 ◁ᵥ ti.(ti_tag) x @ int size_t) v2 (v2 ◁ᵥ n @ int it) op (IntOp size_t) (IntOp it) T) -∗
    typed_bin_op v1 (v1 ◁ᵥ tunion_tag ti x) v2 (v2 ◁ᵥ n @ int it) op (IntOp size_t) (IntOp it) T.
  Proof. by rewrite /(ty_own_val (tunion_tag _ _))/=. Qed.
  Global Instance type_binop_tunion_tag_int_eq_inst it v1 n v2 ti x:
    TypedBinOpVal v1 (tunion_tag ti x) v2 (n @ int it)%I EqOp (IntOp size_t) (IntOp it) :=
    λ T, i2p (type_binop_tunion_tag_int ti x it v1 n v2 T _).
  Global Instance type_binop_tunion_tag_int_ne_inst it v1 n v2 ti x:
    TypedBinOpVal v1 (tunion_tag ti x) v2 (n @ int it)%I NeOp (IntOp size_t) (IntOp it) :=
    λ T, i2p (type_binop_tunion_tag_int ti x it v1 n v2 T _).
  Global Instance type_binop_tunion_tag_int_gt_inst it v1 n v2 ti x:
    TypedBinOpVal v1 (tunion_tag ti x) v2 (n @ int it)%I GtOp (IntOp size_t) (IntOp it) :=
    λ T, i2p (type_binop_tunion_tag_int ti x it v1 n v2 T _).
  Global Instance type_binop_tunion_tag_int_lt_inst it v1 n v2 ti x:
    TypedBinOpVal v1 (tunion_tag ti x) v2 (n @ int it)%I LtOp (IntOp size_t) (IntOp it) :=
    λ T, i2p (type_binop_tunion_tag_int ti x it v1 n v2 T _).
  Global Instance type_binop_tunion_tag_int_ge_inst it v1 n v2 ti x:
    TypedBinOpVal v1 (tunion_tag ti x) v2 (n @ int it)%I GeOp (IntOp size_t) (IntOp it) :=
    λ T, i2p (type_binop_tunion_tag_int ti x it v1 n v2 T _).
  Global Instance type_binop_tunion_tag_int_le_inst it v1 n v2 ti x:
    TypedBinOpVal v1 (tunion_tag ti x) v2 (n @ int it)%I LeOp (IntOp size_t) (IntOp it) :=
    λ T, i2p (type_binop_tunion_tag_int ti x it v1 n v2 T _).


  (*** variant *)
  Program Definition variant (ti : tunion_info) (x : ti.(ti_rtype)) (ty : type) : type := {|
     ty_own β l := l ◁ₗ{β} (padded ty (ti_member ti x).2 (ul_layout ti.(ti_union_layout)))
  |}%I.
  Next Obligation. iIntros (??????). by iApply ty_share. Qed.

  (* TODO: make this not an instance but a definition and add hint similar to padded. Or make a MovableLayout typeclass *)
  Global Program Definition movable_variant ti x ty `{!Movable ty} `{!LayoutEq (ty.(ty_layout)) ((ti_member ti x).2)} : Movable (variant ti x ty) := {|
    ty_layout := (ti.(ti_union_layout));
    ty_own_val v := v ◁ᵥ (padded ty (ti_member ti x).2 (ul_layout ti.(ti_union_layout)));
  |}%I.
  Next Obligation. iIntros (??????) "Hv". rewrite /ty_own/=. by iDestruct (ty_aligned with "Hv") as %?. Qed.
  Next Obligation. iIntros (??????) "Hv". by iDestruct (ty_size_eq with "Hv") as %?. Qed.
  Next Obligation. iIntros (??????) => /=. rewrite /ty_own/=. by apply ty_deref. Qed.
  Next Obligation. iIntros (????????) "Hl Hv" => /=. rewrite /ty_own/=. by iApply (ty_ref with "[] Hl Hv"). Qed.

  Lemma subsume_active_union_variant ti ul x l β ty1 ty2 T n:
    ⌜ti.(ti_union_layout) = ul⌝ ∗ ⌜(ti_member ti x).1 = n⌝ ∗
      subsume (l at_union{ul}ₗ n ◁ₗ{β} ty1) (l at_union{ul}ₗ n ◁ₗ{β} ty2) T -∗
    subsume (l ◁ₗ{β} active_union ul n ty1) (l ◁ₗ{β} variant ti x ty2) T.
  Proof.
    iDestruct 1 as (<- <-) "HT". iDestruct 1 as (ly ->%layout_of_member_ti_member) "Hu". rewrite /variant/GetMemberUnionLoc/=.
    by iApply (padded_mono with "[$HT]").
  Qed.
  Global Instance subsume_active_union_variant_inst ti ul x l β ty1 ty2 n:
    SubsumePlace l β (active_union ul n ty1) (variant ti x ty2) :=
    λ T, i2p (subsume_active_union_variant ti ul x l β ty1 ty2 T n).

  Lemma subsume_variant_variant ti x1 x2 l β ty1 ty2 T:
    ⌜ti.(ti_tag) x1 = ti.(ti_tag) x2⌝ ∗ subsume (l at_union{ti.(ti_union_layout)}ₗ (ti_member ti x1).1 ◁ₗ{β} ty1)
            (l at_union{ti.(ti_union_layout)}ₗ (ti_member ti x1).1 ◁ₗ{β} ty2) T -∗
    subsume (l ◁ₗ{β} variant ti x1 ty1) (l ◁ₗ{β} variant ti x2 ty2) T.
  Proof.
    iDestruct 1 as (Htag) "HT". rewrite !/(ty_own (variant _ _ _))/=/ti_member Htag.
      by iApply (padded_mono with "[$HT]").
  Qed.
  Global Instance subsume_variant_variant_inst ti x1 x2 l β ty1 ty2:
    SubsumePlace l β (variant ti x1 ty1) (variant ti x2 ty2) :=
    λ T, i2p (subsume_variant_variant ti x1 x2 l β ty1 ty2 T).

  Lemma type_place_variant K β T ul n l ty ti x {Heq: TCEq (ti_member ti x).1 n} :
    ⌜ul = ti.(ti_union_layout)⌝ ∗
     typed_place K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, variant ti x (typ t))) -∗
    typed_place (GetMemberUnionPCtx ul n :: K) l β (variant ti x ty) T.
  Proof.
    move: Heq => /TCEq_eq <-.
    iIntros "[-> HP]" (Φ) "Hs HΦ" => /=.
    rewrite {2}/variant /padded/=. iDestruct "Hs" as (??) "[Hb [Hty Hpad]]".
    iApply wp_get_member_union. by apply val_to_of_loc. iExists _. iSplit => //.
    iApply ("HP" with "[Hty]"). by rewrite /GetMemberUnionLoc.
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    rewrite /variant/padded/GetMemberUnionLoc/=. iSplit => //. by iFrame.
  Qed.
  Global Instance type_place_variant_inst K β ul n l ty ti x `{!TCEq (ti_member ti x).1 n}:
    TypedPlace (GetMemberUnionPCtx ul n :: K) l β (variant ti x ty) | 20 :=
    λ T, i2p (type_place_variant K β T ul n l ty ti x).

  Lemma type_place_variant_neq K T ul n l ty `{!Movable ty} ti x :
    (⌜ul = ti.(ti_union_layout)⌝ ∗ ⌜ty.(ty_layout) = (ti_member ti x).2⌝ ∗ ∀ v, v◁ᵥty -∗ typed_place (GetMemberUnionPCtx ul n :: K) l Own (uninit ul) T) -∗
    typed_place (GetMemberUnionPCtx ul n :: K) l Own (variant ti x ty) T.
  Proof.
    iIntros "[-> [% HP]]". rewrite /variant/=. iApply typed_place_subsume.
    iApply subsume_padded_uninit. iIntros (v) "Hv".
    iSplit => //. iIntros "$". by iApply "HP".
  Qed.
  Global Instance type_place_variant_neq_inst K ul n l ty `{!Movable ty} ti x:
    TypedPlace (GetMemberUnionPCtx ul n :: K) l Own (variant ti x ty) | 50:=
    λ T, i2p (type_place_variant_neq K T ul n l ty ti x ).
End function.
Hint Extern 1 (Movable (variant ?ti ?x ?ty)) => simple apply (movable_variant ti x ty) : typeclass_instances.

Section function.
  Context `{!typeG Σ}.
  (*** tunion *)
  Program Definition tunion (ti : tunion_info) : rtype := {|
    rty_type := ti.(ti_rtype);
    rty r := {|
      ty_own β l := l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti r;
         variant ti r (ti.(ti_type) r)
   ] |}%I |}.
  Next Obligation. iIntros (?????). by apply ty_share. Qed.

  Class MovableTUnion (ti : tunion_info) : Type := {
    mti_movable ir :> Movable (ti.(ti_type) ir);
    mti_layout ir :> LayoutEq (ti.(ti_type) ir).(ty_layout) (ti_member ti ir).2;
  }.

  Global Program Instance movable_tunion ti `{!MovableTUnion ti} : RMovable (tunion ti) := {|
    rmovable r := {|
      ty_layout := ti.(ti_base_layout);
      ty_own_val v := ty_own_val (Movable := (@movable_struct _ _ _ _ (ml_cons _ _) _)) (struct ti.(ti_base_layout) [
         tunion_tag ti r;
         variant ti r (ti.(ti_type) r)
   ]) v;
  |}%I |}.
  Next Obligation. move => ????. rewrite ti_base_layout_members. apply _. Qed.
  Next Obligation. iIntros (????) "Hl". rewrite /ty_own/=/ty_own/=. by iDestruct "Hl" as (?) "?". Qed.
  Next Obligation. iIntros (????) "Hv". by iDestruct (ty_size_eq with "Hv") as %?. Qed.
  Next Obligation. iIntros (????) => /=. rewrite /ty_own. by apply ty_deref. Qed.
  Next Obligation. iIntros (??????) "Hl Hv" => /=. rewrite /ty_own/=. by iApply (ty_ref with "[] Hl Hv"). Qed.
  Next Obligation. done. Qed.


  Lemma simplify_hyp_tunion ti x l β T:
    (l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ] -∗ T) -∗ simplify_hyp (l◁ₗ{β} x @ tunion ti) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simplify_hyp_tunion_inst ti x l β :
    SimplifyHypPlace l β (x @ tunion ti)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_tunion ti x l β T).

  Lemma simplify_goal_tunion ti x l β T:
    T (l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ]) -∗ simplify_goal (l◁ₗ{β} x @ tunion ti) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "?". Qed.
  Global Instance simplify_goal_tunion_inst ti x l β :
    SimplifyGoalPlace l β (x @ tunion ti)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_tunion ti x l β T).

End function.

Typeclasses Opaque variant.
