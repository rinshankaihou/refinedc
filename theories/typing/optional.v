From refinedc.typing Require Export type.
From refinedc.typing Require Import programs int.
Set Default Proof Using "Type".

(** We need to use this unbundled approach to ensure that ROptionable
uses the same instances as Optionable.
  TODO: findout if there is a better way, maybe using Canonical Structures?
 *)
Class Optionable `{!typeG Σ} (ty : type) `{!Movable ty} (optty : type) `{!Movable optty} (ot1 ot2 : op_type) := {
  opt_pre : val → val → iProp Σ;
  opt_alt_sz : optty.(ty_layout) = ty.(ty_layout);
  opt_bin_op (bty beq : bool) v1 v2 σ v :
    (⊢ opt_pre v1 v2 -∗ (if bty then v1 ◁ᵥ ty else v1 ◁ᵥ optty) -∗ v2 ◁ᵥ optty -∗ state_ctx σ -∗
        ⌜eval_bin_op (if beq then EqOp else NeOp) ot1 ot2 σ v1 v2 v ↔ val_of_Z (Z_of_bool (xorb bty beq)) i32 = Some v⌝);
}.
Arguments opt_pre {_ _} _ {_ _ _ _ _ _} _ _.

Class ROptionable `{!typeG Σ} (r : rtype) `{!RMovable r} (optty : type) `{!Movable optty} (ot1 ot2 : op_type) := {
  ropt_opt x :> Optionable (r.(rty) x) optty ot1 ot2;
}.

Class OptionableAgree `{!typeG Σ} (ty1 ty2 : type) : Prop :=
  optionable_dist : True.

Section optional.
  Context `{!typeG Σ}.

  Global Program Instance optionable_ty_of_rty r `{!RMovable r} `{!Inhabited (r.(rty_type))} optty `{!Movable optty} ot1 ot2 `{!ROptionable r optty ot1 ot2}: Optionable r optty ot1 ot2 := {|
    opt_pre v1 v2 := (∀ x, opt_pre (r.(rty) x) v1 v2)%I
  |}.
  Next Obligation. move => r???????. by rewrite ->opt_alt_sz. Qed.
  Next Obligation.
    iIntros(r??????? bty beq v1 v2 σ v) "Hpre Hv1 Hv2".
    destruct bty. iDestruct "Hv1" as (y) "Hv1".
    all: iApply (opt_bin_op with "Hpre [Hv1] Hv2") => /= //.
    Unshelve.
    apply inhabitant.
  Qed.

  Global Instance optionable_agree_wr1 (ty1 : rtype) p ty2 `{!OptionableAgree ty1 ty2} : OptionableAgree (p @ ty1) ty2.
  Proof. done. Qed.
  Global Instance optionable_agree_wr2 (ty2 : rtype) p ty1 `{!OptionableAgree ty1 ty2} : OptionableAgree ty1 (p @ ty2).
  Proof. done. Qed.
  Global Instance optionable_agree_id ty : OptionableAgree ty ty.
  Proof. done. Qed.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition optional_type (ty : type) (optty : type) (b : Prop) : type := {|
      ty_own β l := (⌜b⌝ ∗ l◁ₗ{β}ty ∨ ⌜¬b⌝ ∗ l◁ₗ{β}optty)%I
  |}.
  Next Obligation.
    iIntros (??????).
    by iDestruct 1 as "[[% H]|[% H]]";iMod (ty_share with "H") => //; iModIntro; [iLeft | iRight ]; iFrame.
  Qed.
  Global Instance optional_type_ne n : Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) optional_type.
  Proof. solve_type_proper. Qed.
  Global Instance optional_type_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) optional_type.
  Proof. solve_type_proper. Qed.

  (* Never use optional without the refinement! This will fail
  horribly since the implicit refinement might not be decidable! Use
  optionalO with () instead. *)
  Program Definition optional (ty : type) (optty : type) : rtype := {|
    rty_type := Prop;
    rty := optional_type ty optty
  |}.

  (* it is important that the layout of an optional computes without
  doing case distrinction on the boolean. Otherwise it is very
  annoying to use. *)
  Global Program Instance rmovable_optional ty  `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2} : RMovable (optional ty optty) := {|
    rmovable b := {|
      ty_layout := optty.(ty_layout);
      ty_own_val v := (⌜b⌝ ∗ v◁ᵥty ∨ ⌜¬b⌝ ∗ v◁ᵥoptty)%I
  |} |}.
  Next Obligation.
    iIntros (ty?????? b ?). iDestruct 1 as "[[% Hv]|[% Hv]]";iDestruct (ty_aligned with "Hv") as %? => //.
      by rewrite opt_alt_sz.
  Qed.
  Next Obligation.
    iIntros (ty?????? b ?). iDestruct 1 as "[[% Hv]|[% Hv]]";iDestruct (ty_size_eq with "Hv") as %? => //.
      by rewrite opt_alt_sz.
  Qed.
  Next Obligation.
    iIntros (ty ? optty ???? b l) "Hl".
    iDestruct "Hl" as "[[% Hl]|[% Hl]]"; iDestruct (ty_deref with "Hl") as (?) "[? ?]"; eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ty ? optty ???? b l v ?) "Hl Hv".
    iDestruct "Hv" as "[[% Hv]|[% Hv]]"; iDestruct (ty_ref with "[] Hl Hv") as "H"; rewrite -?opt_alt_sz//;
       [iLeft | iRight]; by iFrame.
  Qed.
  Next Obligation. done. Qed.

  Global Instance optional_loc_in_bounds ty e ot β n `{!LocInBounds ty β n} `{!LocInBounds ot β n}:
    LocInBounds (e @ optional ty ot) β n.
  Proof.
    constructor. rewrite /with_refinement /=. iIntros (l) "Hl".
    iDestruct "Hl" as "[[_ Hl]|[_ Hl]]"; by iApply (loc_in_bounds_in_bounds with "Hl").
  Qed.

  (* We could add rules like *)
  (* Lemma simplify_optional_goal ty optty l β T b `{!Decision b}: *)
  (*   T (if decide b then l◁ₗ{β}ty else l◁ₗ{β}optty) -∗ *)
  (*   simplify_goal (l◁ₗ{β} b @ optional ty optty) T. *)
  (* but that would lead to the automation doing a case split out of
  despair which is not a good user experience. Thus you should make
  sure that the other rules in this file work for you, which don't
  cause unnecssary case splits. *)

  (* TODO: should be allow different opttys? *)
  Global Instance simple_subsume_place_optional ty1 ty2 optty b1 b2 `{!SimpleSubsumePlace ty1 ty2 P}:
    SimpleSubsumePlace (b1 @ optional ty1 optty) (b2 @ optional ty2 optty) (⌜b1 ↔ b2⌝ ∗ P).
  Proof.
    iIntros (l β) "HP Hl". iDestruct "HP" as (Hequiv) "HP".
    iDestruct "Hl" as "[[% Hl]|[% Hl]]"; [iLeft | iRight]; rewrite -Hequiv. 2: by iFrame.
    iSplit => //. iApply (@simple_subsume_place with "HP Hl").
  Qed.

  Global Instance simple_subsume_val_optional ty1 ty2 optty b1 b2 ot1 ot2
       `{!Movable ty1} `{!Movable ty2} `{!Movable optty}
       `{!Optionable ty1 optty ot1 ot2} `{!Optionable ty2 optty ot1 ot2}
       `{!SimpleSubsumeVal ty1 ty2 P}:
    SimpleSubsumeVal (b1 @ optional ty1 optty) (b2 @ optional ty2 optty) (⌜b1 ↔ b2⌝ ∗ P).
  Proof.
    iIntros (v) "[Heq P] H". rewrite /ty_own_val /=. iDestruct "Heq" as %->.
    iDestruct "H" as "[[?H] | [??]]"; last (iRight; by iFrame).
    iLeft. iFrame. iApply (simple_subsume_val with "P H").
  Qed.

  Lemma subsume_optional_optty_ref b ty optty l β T:
    ⌜¬ b⌝ ∗ T -∗ subsume (l ◁ₗ{β} optty) (l ◁ₗ{β} b @ optional ty optty) T.
  Proof. iIntros "[Hb $] Hl". iRight. by iFrame. Qed.
  Global Instance subsume_optional_optty_ref_inst b ty optty l β:
    SubsumePlace l β (optty) (b @ optional ty optty)%I :=
    λ T, i2p (subsume_optional_optty_ref b ty optty l β T).

  Lemma subsume_optional_ty_ref b ty ty' optty l β T:
    ⌜b⌝ ∗ subsume (l ◁ₗ{β} ty') (l ◁ₗ{β} ty) T -∗ subsume (l ◁ₗ{β} ty') (l ◁ₗ{β} b @ optional ty optty) T.
  Proof. iIntros "[Hb Hsub] Hl". iDestruct ("Hsub" with "Hl") as "[? $]". iLeft. by iFrame. Qed.
  Global Instance subsume_optional_ty_ref_inst b ty ty' optty l β `{!OptionableAgree ty ty'}:
    SubsumePlace l β ty' (b @ optional ty optty)%I :=
    λ T, i2p (subsume_optional_ty_ref b ty ty' optty l β T).

  Lemma subsume_optional_val_optty_ref b ty optty v T `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2}:
    ⌜¬ b⌝ ∗ T -∗ subsume (v ◁ᵥ optty) (v ◁ᵥ b @ optional ty optty) T.
  Proof. iIntros "[Hb $] Hl". iRight. by iFrame. Qed.
  Global Instance subsume_optional_val_optty_ref_inst b ty optty v `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2}:
    SubsumeVal v (optty) (b @ optional ty optty)%I :=
    λ T, i2p (subsume_optional_val_optty_ref b ty optty v T ot1 ot2).

  Lemma subsume_optional_val_ty_ref b ty ty' optty v T `{!Movable ty} `{!Movable ty'} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2}:
    ⌜b⌝ ∗ subsume (v ◁ᵥ ty') (v ◁ᵥ ty) T -∗ subsume (v ◁ᵥ ty') (v ◁ᵥ b @ optional ty optty) T.
  Proof. iIntros "[Hb Hsub] Hl". iDestruct ("Hsub" with "Hl") as "[? $]". iLeft. by iFrame. Qed.
  Global Instance subsume_optional_val_ty_ref_inst b ty ty' optty v `{!Movable ty} `{!Movable ty'} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2} `{!OptionableAgree ty ty'}:
    SubsumeVal v ty' (b @ optional ty optty)%I :=
    λ T, i2p (subsume_optional_val_ty_ref b ty ty' optty v T ot1 ot2).

  Inductive destruct_hint_optional :=
  | DestructHintOptionalEq (P : Prop)
  | DestructHintOptionalNe (P : Prop).

  Lemma type_eq_optional_refined v1 v2 ty optty `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2} T b :
    opt_pre ty v1 v2 ∧
    destruct_hint DHintInfo (DestructHintOptionalEq b) (⌜b⌝ -∗ v1 ◁ᵥ ty -∗ T (i2v (Z_of_bool false) i32) (t2mt (false @ boolean i32))) ∧
    destruct_hint DHintInfo (DestructHintOptionalEq (¬ b)) (⌜¬ b⌝ -∗ v1 ◁ᵥ optty -∗ T (i2v (Z_of_bool true) i32) (t2mt (true @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ b @ (optional ty optty)) v2 (v2 ◁ᵥ optty) EqOp ot1 ot2 T.
  Proof.
    unfold destruct_hint. iIntros "HT Hv1 Hv2" (Φ) "HΦ".
    iDestruct "Hv1" as "[[% Hv1]|[% Hv1]]".
    - iApply (wp_binop_det (i2v (Z_of_bool false) i32)). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op true true with "Hpre Hv1 Hv2 Hctx") as %->.
        iPureIntro. rewrite /i2v.
        have [|v' ->] := val_of_Z_is_Some i32 (Z_of_bool false) => //.
        naive_solver.
      }
      iDestruct "HT" as "[_ [HT _]]".
      iDestruct ("HT" with "[//] Hv1") as "HT".
      by iApply ("HΦ" with "[] HT").
    - iApply (wp_binop_det (i2v (Z_of_bool true) i32)). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op false true with "Hpre Hv1 Hv2 Hctx") as %->.
        iPureIntro. rewrite /i2v.
        have [|v' ->] := val_of_Z_is_Some i32 (Z_of_bool true) => //.
        naive_solver.
      }
      iDestruct "HT" as "[_ [_ HT]]".
      iDestruct ("HT" with "[//] Hv1") as "HT".
      by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_eq_optional_refined_inst v1 v2 ty optty `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2} b :
    TypedBinOp v1 (v1 ◁ᵥ b @ (optional ty optty))%I v2 (v2 ◁ᵥ optty) EqOp ot1 ot2 :=
    λ T, i2p (type_eq_optional_refined v1 v2 ty optty ot1 ot2 T b).

  Lemma type_eq_optional_neq v1 v2 ty optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!Optionable ty optty ot1 ot2} T :
    opt_pre ty v1 v2 ∧
    (∀ v, v1 ◁ᵥ ty -∗ T v (t2mt (false @ boolean i32)) ) -∗
      typed_bin_op v1 (v1 ◁ᵥ ty) v2 (v2 ◁ᵥ optty) EqOp ot1 ot2 T.
  Proof.
    iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ".
    have [|v' Hv] := val_of_Z_is_Some i32 (Z_of_bool false) => //.
    iApply (wp_binop_det v'). iSplit. {
      iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
      iDestruct (opt_bin_op true true with "Hpre Hv1 Hv2 Hctx") as %->.
      iPureIntro. by split => ?; simpl in *; simplify_eq.
    }
    iDestruct ("HT" with "Hv1") as "HT".
    iApply "HΦ" => //. iPureIntro. by apply val_to_of_Z.
  Qed.

  Global Instance type_eq_optional_neq_inst v1 v2 ty optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!Optionable ty optty ot1 ot2} :
    TypedBinOp v1 (v1 ◁ᵥ ty) v2 (v2 ◁ᵥ optty) EqOp ot1 ot2 :=
    λ T, i2p (type_eq_optional_neq v1 v2 ty optty ot1 ot2 T).

  Lemma type_neq_optional v1 v2 ty optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!Optionable ty optty ot1 ot2} T b :
    opt_pre ty v1 v2 ∧
    destruct_hint DHintInfo (DestructHintOptionalNe b) (⌜b⌝ -∗ v1 ◁ᵥ ty -∗ T (i2v (Z_of_bool true) i32) (t2mt (true @ boolean i32))) ∧
    destruct_hint DHintInfo (DestructHintOptionalNe (¬ b)) (⌜¬ b⌝ -∗ v1 ◁ᵥ optty -∗ T (i2v (Z_of_bool false) i32) (t2mt (false @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ b @ (optional ty optty)) v2 (v2 ◁ᵥ optty) NeOp ot1 ot2 T.
  Proof.
    unfold destruct_hint. iIntros "HT Hv1 Hv2" (Φ) "HΦ".
    iDestruct "Hv1" as "[[% Hv1]|[% Hv1]]".
    - iApply (wp_binop_det (i2v (Z_of_bool true) i32)). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op true false with "Hpre Hv1 Hv2 Hctx") as %->.
        iPureIntro. rewrite /i2v.
        have [|v' ->] := val_of_Z_is_Some i32 (Z_of_bool true) => //.
        naive_solver.
      }
      iDestruct "HT" as "[_ [HT _]]".
      iDestruct ("HT" with "[//] Hv1") as "HT".
      by iApply ("HΦ" with "[] HT").
    - iApply (wp_binop_det (i2v (Z_of_bool false) i32)). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op false false with "Hpre Hv1 Hv2 Hctx") as %->.
        iPureIntro. rewrite /i2v.
        have [|v' ->] := val_of_Z_is_Some i32 (Z_of_bool false) => //.
        naive_solver.
      }
      iDestruct "HT" as "[_ [_ HT]]".
      iDestruct ("HT" with "[//] Hv1") as "HT".
      by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_neq_optional_inst v1 v2 ty optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!Optionable ty optty ot1 ot2} b :
    TypedBinOp v1 (v1 ◁ᵥ b @ (optional ty optty))%I v2 (v2 ◁ᵥ optty) NeOp ot1 ot2 :=
    λ T, i2p (type_neq_optional v1 v2 ty optty ot1 ot2 T b).

  Global Instance strip_guarded_optional b ty ty' optty E1 E2 β `{!StripGuarded β E1 E2 ty ty'}:
    StripGuarded β E1 E2 (b @ optional ty optty) (b @ optional ty' optty ).
  Proof.
    iIntros (l E HE1 HE2) "Hs".
    iDestruct "Hs" as "[[?Hs]|[?Hs]]"; [iLeft|iRight]; iFrame.
    1: by iDestruct (strip_guarded with "Hs") as "Hs".
    iApply step_fupd_intro => //. solve_ndisj.
  Qed.

  Global Program Instance optional_copyable b ty optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!Optionable ty optty ot1 ot2} `{!Copyable ty} `{!Copyable optty} : Copyable (b @ optional ty optty).
  Next Obligation.
    iIntros (b ty optty ot1 ot2 ? ? ? ? ? E l ?) "[[% Hl]|[% Hl]]".
    all: iMod (copy_shr_acc with "Hl") as (?? ?) "[?[??]]" => //.
    all: iModIntro; iSplit => //; rewrite /=?opt_alt_sz => //; iExists _, _; iFrame.
    by iLeft; iFrame.
    by iRight; iFrame.
  Qed.

End optional.
Typeclasses Opaque optional_type.
Notation "optional< ty , optty >" := (optional ty optty)
  (only printing, format "'optional<' ty ,  optty '>'") : printing_sugar.

Notation "'optional' == ... : P" := (DestructHintOptionalEq P) (at level 100, only printing).
Notation "'optional' != ... : P" := (DestructHintOptionalNe P) (at level 100, only printing).

Section optionalO.
  Context `{!typeG Σ}.

  Program Definition optionalO {A : Type} (ty : A → type) (optty : type) : rtype := {|
    rty_type := option A;
    rty b := if b is Some x return _ then ty x else optty
  |}.

  Global Program Instance rmovable_optionalO A (ty : A → type) ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} : RMovable (optionalO ty optty) := {|
    rmovable b := {|
      ty_layout := optty.(ty_layout);
      ty_own_val v := (if b is Some x return _ then v◁ᵥ(ty x) else v◁ᵥoptty)%I
  |} |}.
  Next Obligation.
    iIntros (A ty?????? [x|] ?) "Hv";iDestruct (ty_aligned with "Hv") as %Ha => //.
    by rewrite -opt_alt_sz in Ha.
  Qed.
  Next Obligation.
    iIntros (A ty?????? [] v) "Hv";iDestruct (ty_size_eq with "Hv") as %Ha => //.
    by rewrite -opt_alt_sz in Ha.
  Qed.
  Next Obligation.
    iIntros (A ty ? optty ???? [] l) "Hl"; rewrite /with_refinement/ty_own/=; iDestruct (ty_deref with "Hl") as (?) "[? ?]"; eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (A ty ? optty ???? [] l v ?) "Hl Hv"; iApply (ty_ref with "[] Hl Hv") => //.
    by rewrite -opt_alt_sz.
  Qed.
  Next Obligation. done. Qed.

  Global Instance optionalO_loc_in_bounds A (ty : A → type) e ot β n `{!∀ x, LocInBounds (ty x) β n} `{!LocInBounds ot β n}:
    LocInBounds (e @ optionalO ty ot) β n.
  Proof.
    constructor. iIntros (l) "Hl". rewrite /with_refinement /=.
    destruct e; by iApply (loc_in_bounds_in_bounds with "Hl").
  Qed.

  (* TODO: should be allow different opttys? *)
  Global Instance simple_subsume_place_optionalO A (ty1 : A → _) ty2 optty b `{!∀ x, SimpleSubsumePlace (ty1 x) (ty2 x) P}:
    SimpleSubsumePlaceR (optionalO ty1 optty) (optionalO ty2 optty) b b P.
  Proof. iIntros (l β) "HP Hl". destruct b. 2: by iFrame. iApply (@simple_subsume_place with "HP Hl"). Qed.

  (* TODO: Should we have more instances like this? E.g. for the goal or for values? *)
  Lemma simpl_hyp_optionalO_Some A (ty : A → type) optty l β x T:
    (l ◁ₗ{β} ty x -∗ T) -∗ simplify_hyp (l ◁ₗ{β} Some x @ optionalO ty optty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simpl_hyp_optionalO_Some_inst A (ty : A → type) optty l β x:
    SimplifyHypPlace l β (Some x @ optionalO ty optty) (Some 0%N) :=
    λ T, i2p (simpl_hyp_optionalO_Some A ty optty l β x T).
  Lemma simpl_hyp_optionalO_None A (ty : A → type) optty l β T:
    (l ◁ₗ{β} optty -∗ T) -∗ simplify_hyp (l ◁ₗ{β} None @ optionalO ty optty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simpl_hyp_optionalO_None_inst A (ty : A → type) optty l β:
    SimplifyHypPlace l β (None @ optionalO ty optty) (Some 0%N) :=
    λ T, i2p (simpl_hyp_optionalO_None A ty optty l β T).

  Lemma subsume_optionalO_optty A (ty : A → type) optty l β T b:
    ⌜b = None⌝ ∗ T -∗ subsume (l ◁ₗ{β} optty) (l ◁ₗ{β} b @ optionalO ty optty) T.
  Proof. by iIntros "[-> $] Hl". Qed.
  Global Instance subsume_optionalO_optty_inst A (ty : A → type) optty l β b:
    SubsumePlace l β (optty) (b @ optionalO ty optty)%I | 10 :=
    λ T, i2p (subsume_optionalO_optty A ty optty l β T b).

  Lemma subsume_optionalO_ty A (ty : A → type) optty l β T b ty':
    (⌜is_Some b⌝ ∗ ∀ x, ⌜b = Some x⌝ -∗ subsume (l ◁ₗ{β} ty') (l ◁ₗ{β} ty x) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ₗ{β} b @ optionalO ty optty) T.
  Proof. iDestruct 1 as ([x ->]) "Hsub". iIntros "Hl". by iApply "Hsub". Qed.
  Global Instance subsume_optionalO_ty_inst A (ty : A → type) optty l β b ty' `{!∀ x, OptionableAgree (ty x) ty'}:
    SubsumePlace l β ty' (b @ optionalO ty optty)%I | 20 :=
    λ T, i2p (subsume_optionalO_ty A ty optty l β T b ty').

  Lemma subsume_optionalO_optty_val A (ty : A → type) optty v T b `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2}:
    ⌜b = None⌝ ∗ T -∗ subsume (v ◁ᵥ optty) (v ◁ᵥ b @ optionalO ty optty) T.
  Proof. by iIntros "[-> $] Hl". Qed.
  Global Instance subsume_optionalO_optty_val_inst A (ty : A → type) optty v b `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2}:
    SubsumeVal v (optty) (b @ optionalO ty optty)%I | 10 :=
    λ T, i2p (subsume_optionalO_optty_val A ty optty v T b).

  Lemma subsume_optionalO_ty_val A (ty : A → type) optty v T b ty' `{!Movable ty'} `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2}:
    (⌜is_Some b⌝ ∗ ∀ x, ⌜b = Some x⌝ -∗ subsume (v ◁ᵥ ty') (v ◁ᵥ ty x) T) -∗ subsume (v ◁ᵥ ty') (v ◁ᵥ b @ optionalO ty optty) T.
  Proof. iDestruct 1 as ([x ->]) "Hsub". iIntros "Hl". by iApply "Hsub". Qed.
  Global Instance subsume_optionalO_ty_val_inst A (ty : A → type) optty v b ty' `{!Movable ty'} `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} `{!∀ x, OptionableAgree (ty x) ty'}:
    SubsumeVal v ty' (b @ optionalO ty optty)%I | 20 :=
    λ T, i2p (subsume_optionalO_ty_val A ty optty v T b ty').

  Lemma subsume_optional_optionalO_val ty optty b T v `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2}:
    T -∗
    subsume (v ◁ᵥ b @ optional ty optty) (v ◁ᵥ optionalO (λ _ : (), ty) optty) T.
  Proof. iIntros "$ [[% ?]|[% ?]]"; [iExists (Some ())|iExists None]; iFrame. Qed.
  Global Instance subsume_optional_optionalO_val_inst ty optty b v `{!Movable ty} `{!Movable optty} ot1 ot2 `{!Optionable ty optty ot1 ot2} :
    SubsumeVal v (b @ optional ty optty) (optionalO (λ _ : (), ty) optty) :=
    λ T, i2p (subsume_optional_optionalO_val ty optty b T v ot1 ot2).

  Inductive destruct_hint_optionalO :=
  | DestructHintOptionalO.

  Lemma type_eq_optionalO A v1 v2 (ty : A → type) optty ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} T b `{!Inhabited A} :
    opt_pre (ty (default inhabitant b)) v1 v2 ∧
    destruct_hint (DHintDestruct _ b) DestructHintOptionalO
      (∀ v, (if b  is Some x then v1 ◁ᵥ ty x else v1 ◁ᵥ optty) -∗ T v (t2mt ((if b is Some x then false else true) @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ b @ optionalO ty optty) v2 (v2 ◁ᵥ optty) EqOp ot1 ot2 T.
  Proof.
    unfold destruct_hint. iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ".
    destruct b.
    - have [|v' Hv] := val_of_Z_is_Some i32 (Z_of_bool false) => //.
      iApply (wp_binop_det v'). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op true true with "Hpre [Hv1] [Hv2] Hctx") as %->.
        iFrame. iFrame. iPureIntro. by split => ?; simpl in *; simplify_eq.
      }
      iDestruct ("HT" with "Hv1") as "HT".
      iApply "HΦ" => //. iPureIntro. by apply val_to_of_Z.
    - have [|v' Hv] := val_of_Z_is_Some i32 (Z_of_bool true) => //.
      iApply (wp_binop_det v'). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op false true with "Hpre [Hv1] [Hv2] Hctx") as %->.
        iFrame. iFrame. iPureIntro. by split => ?; simpl in *; simplify_eq.
      }
      iDestruct ("HT" with "Hv1") as "HT".
      iApply "HΦ" => //. iPureIntro. by apply val_to_of_Z.
  Qed.

  Global Instance type_eq_optionalO_inst A v1 v2 (ty : A → type) optty ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} b `{!Inhabited A} :
    TypedBinOp v1 (v1 ◁ᵥ b @ optionalO ty optty)%I v2 (v2 ◁ᵥ optty) EqOp ot1 ot2 :=
    λ T, i2p (type_eq_optionalO A v1 v2 ty optty ot1 ot2 T b).

  Lemma type_neq_optionalO A v1 v2 (ty : A → type) optty ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} T b `{!Inhabited A} :
    opt_pre (ty (default inhabitant b)) v1 v2 ∧
    destruct_hint (DHintDestruct _ b) DestructHintOptionalO
      (∀ v, (if b is Some x then v1 ◁ᵥ ty x else v1 ◁ᵥ optty) -∗ T v (t2mt ((if b is Some x then true else false) @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ b @ optionalO ty optty) v2 (v2 ◁ᵥ optty) NeOp ot1 ot2 T.
  Proof.
    unfold destruct_hint. iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ".
    destruct b.
    - have [|v' Hv] := val_of_Z_is_Some i32 (Z_of_bool true) => //.
      iApply (wp_binop_det v'). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op true false with "Hpre [Hv1] [Hv2] Hctx") as %->.
        iFrame. iFrame. iPureIntro. by split => ?; simpl in *; simplify_eq.
      }
      iDestruct ("HT" with "Hv1") as "HT".
      iApply "HΦ" => //. iPureIntro. by apply val_to_of_Z.
    - have [|v' Hv] := val_of_Z_is_Some i32 (Z_of_bool false) => //.
      iApply (wp_binop_det v'). iSplit. {
        iIntros (σ v) "Hctx". iDestruct "HT" as "[Hpre _]".
        iDestruct (opt_bin_op false false with "Hpre [Hv1] [Hv2] Hctx") as %->.
        iFrame. iFrame. iPureIntro. by split => ?; simpl in *; simplify_eq.
      }
      iDestruct ("HT" with "Hv1") as "HT".
      iApply "HΦ" => //. iPureIntro. by apply val_to_of_Z.
  Qed.
  Global Instance type_neq_optionalO_inst A v1 v2 (ty : A → type) optty ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} b `{!Inhabited A} :
    TypedBinOp v1 (v1 ◁ᵥ b @ optionalO ty optty)%I v2 (v2 ◁ᵥ optty) NeOp ot1 ot2 :=
    λ T, i2p (type_neq_optionalO A v1 v2 ty optty ot1 ot2 T b).

  Lemma read_optionalO_case A l b (ty : A → type) optty ly (T : val → type → _) a:
    destruct_hint (DHintDestruct _ b) DestructHintOptionalO (typed_read_end a l Own (if b is Some x then ty x else optty) ly T) -∗
      typed_read_end a l Own (b @ optionalO ty optty) ly T.
  Proof. by destruct b. Qed.
  (* This should be tried very late *)
  Global Instance read_optionalO_case_inst A l b (ty : A → type) optty ly a:
    TypedReadEnd a l Own (b @ optionalO ty optty) ly | 1001 :=
    λ T, i2p (read_optionalO_case A l b ty optty ly T a).


  Global Instance strip_guarded_optionalO A x E1 E2 (ty : A → type) ty' optty β `{!∀ y, StripGuarded β E1 E2 (ty y) (ty' y)}:
    StripGuarded β E1 E2 (x @ optionalO ty optty) (x @ optionalO ty' optty).
  Proof.
    iIntros (l E HE1 HE2) "Hs".
    destruct x as [x|]; first by iDestruct (strip_guarded with "Hs") as "Hs".
    iFrame. iApply step_fupd_intro => //. solve_ndisj.
  Qed.

  Global Instance strip_guarded_optionalO_unrefined A E1 E2 (ty : A → type) ty' optty β `{!∀ y, StripGuarded β E1 E2 (ty y) (ty' y)}:
    StripGuarded β E1 E2 (optionalO ty optty) (optionalO ty' optty).
  Proof.
    iIntros (l E HE1 HE2). iDestruct 1 as (x) "Hs". iExists x.
    destruct x as [x|]; first by iDestruct (strip_guarded with "Hs") as "Hs".
    iFrame. iApply step_fupd_intro => //. solve_ndisj.
  Qed.

  Global Program Instance optionalO_copyable A (ty : A → type) optty x ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} `{!∀ x, Copyable (ty x)} `{!Copyable optty} : Copyable (x @ optionalO ty optty).
  Next Obligation.
    iIntros (A ty optty x ot1 ot2 ? ? ? ? ? E l ?). destruct x.
    all: iIntros "Hl".
    all: iMod (copy_shr_acc with "Hl") as (Hl ? ?) "[?[??]]" => //.
    all: iModIntro; iSplit => //=.
    1: by rewrite -opt_alt_sz in Hl.
    all: iExists _, _; iFrame.
  Qed.
End optionalO.
Notation "optionalO< ty , optty >" := (optional ty optty)
  (only printing, format "'optionalO<' ty ,  optty '>'") : printing_sugar.

Section int_optional.
  Context `{!typeG Σ}.

  Global Program Instance int_neg_optional (n : nat) it :
    Optionable (n @ int it) ((-1) @ int it)%I (IntOp it) (IntOp it) := {|
    opt_pre _ _ := True%I
  |}.
  Next Obligation. by move => ??. Qed.
  Next Obligation.
    iIntros (?? [] [] ????) "_ %Hv1 %Hv2 _ !%".
    all: split; first by (move => Hstep; inversion Hstep; simplify_eq; case_bool_decide => //=; lia).
    all: rewrite val_of_Z_bool => ?; simplify_eq; econstructor => //; case_bool_decide => //; lia.
  Qed.
End int_optional.
