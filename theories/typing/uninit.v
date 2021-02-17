From refinedc.typing Require Export type.
From refinedc.typing Require Import programs int own.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit (ly : layout) : type := {|
    ty_own β l := (l ↦[β]|ly|)%I;
  |}.
  Next Obligation. iIntros (????). iApply heap_mapsto_own_state_exist_share. Qed.

  Global Program Instance movable_uninit ly : Movable (uninit ly) := {|
    ty_layout := ly;
    ty_own_val v := ⌜v `has_layout_val` ly⌝%I;
  |}.
  Next Obligation. iIntros (ly l). by iDestruct 1 as (???) "?". Qed.
  Next Obligation. by iIntros (ly v ?). Qed.
  Next Obligation.
    iIntros (ly l) "Hl". iDestruct "Hl" as (???) "?".
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ly l v ?) "Hl ?". iExists _. by iFrame.
  Qed.

  Lemma uninit_loc_in_bounds l β ly :
    l ◁ₗ{β} uninit ly -∗ loc_in_bounds l (ly_size ly).
  Proof.
    iIntros "Hl". iDestruct "Hl" as (v <-) "[_ Hl]".
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.

  Global Instance loc_in_bounds_uninit ly β: LocInBounds (uninit ly) β (ly_size ly).
  Proof.
    constructor. iIntros (l) "Hl".
    by iDestruct (uninit_loc_in_bounds with "Hl") as "#Hb".
  Qed.

  (* This only works for own because of ty might have interior mutability. *)
  Lemma uninit_mono l ty `{!Movable ty} ly T `{!FastDone (ty.(ty_layout) = ly)}:
    (∀ v, v ◁ᵥ ty -∗ T) -∗
    subsume (l ◁ₗ ty) (l ◁ₗ uninit ly) T.
  Proof.
    unfold FastDone in *; subst. iIntros "HT Hl".
    iDestruct (ty_aligned with "Hl") as %?.
    iDestruct (ty_deref with "Hl") as (v) "[Hmt Hv]".
    iDestruct (ty_size_eq with "Hv") as %?.
    iSplitL "Hmt".
    - iExists _. by iFrame.
    - by iApply "HT".
  Qed.
  (* This cannot be a definition but must be an Hint Extern since
  Movable is a dependent subgoal and thus gets shelved. *)
  Definition uninit_mono_inst l ty `{!Movable ty} ly `{!FastDone (ty.(ty_layout) = ly)}:
    SubsumePlace l Own ty (uninit ly) :=
    λ T, i2p (uninit_mono l ty ly T).

  Lemma subsume_uninit_eq l β ly1 ly2 T `{!CanSolve (ly1.(ly_size) = ly2.(ly_size))}:
    (⌜l `has_layout_loc` ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗ T) -∗
    subsume (l ◁ₗ{β} uninit ly1) (l ◁ₗ{β} uninit ly2) T.
  Proof.
    revert select (CanSolve _) => Hsz. unfold CanSolve in *.
    iIntros "HT Hl".
    iDestruct "Hl" as (v Hv Hl) "Hl".
    iDestruct ("HT" with "[//]") as (?) "$".
    iExists _. iFrame. by rewrite /has_layout_val -Hsz.
  Qed.
  Global Instance subsume_uninit_eq_inst l β ly1 ly2 `{!CanSolve (ly1.(ly_size) = ly2.(ly_size))} :
    SubsumePlace l β (uninit ly1) (uninit ly2) | 10 :=
    λ T, i2p (subsume_uninit_eq l β ly1 ly2 T).

  Lemma split_uninit n l β ly1:
    (n ≤ ly1.(ly_size))%nat →
    l ◁ₗ{β} uninit ly1 -∗
      l ◁ₗ{β} uninit (ly_set_size ly1 n) ∗ (l +ₗ n) ◁ₗ{β} (uninit (ly_offset ly1 n)).
  Proof.
    iIntros (?) "Hl". rewrite /ty_own/=.
    iDestruct "Hl" as (v Hv Hl) "Hmt".
    rewrite -[v](take_drop n) heap_mapsto_own_state_app.
    iDestruct "Hmt" as "[Hmt1 Hmt2]". iSplitL "Hmt1".
    - iExists _. iFrame. iSplit => //. rewrite /has_layout_val take_length_le // Hv //.
    - rewrite take_length_le ?Hv //.
      iExists _. iFrame. rewrite /has_layout_val drop_length Hv. iSplit => //.
      iPureIntro. by apply has_layout_ly_offset.
  Qed.

  Lemma merge_uninit ly1 ly2 l β:
    (ly1.(ly_size) ≤ ly2.(ly_size))%nat →
    (ly_align ly2 ≤ ly_align ly1)%nat →
    l ◁ₗ{β} uninit ly1 -∗ (l +ₗ ly1.(ly_size)) ◁ₗ{β} (uninit (ly_offset ly2 ly1.(ly_size))) -∗
      l ◁ₗ{β} uninit ly2.
  Proof.
    iIntros (? ?) "Hl1 Hl2". rewrite /ty_own/=.
    iDestruct "Hl1" as (v1 Hv1 Hl1) "Hmt1".
    iDestruct "Hl2" as (v2 Hv2 Hl2) "Hmt2".
    iExists (v1 ++ v2).
    rewrite heap_mapsto_own_state_app Hv1 /has_layout_val app_length Hv1 Hv2.
    iFrame. iPureIntro. split.
    - rewrite {2}/ly_size/=. lia.
    - by apply: has_layout_loc_trans'.
  Qed.

  Lemma subsume_uninit_merge l β ly1 ly2 T `{!CanSolve (ly1.(ly_size) ≤ ly2.(ly_size))%nat}:
    (⌜ly_align ly2 ≤ ly_align ly1⌝%nat ∗ ((l +ₗ ly1.(ly_size)) ◁ₗ{β} uninit (ly_offset ly2 ly1.(ly_size)) ∗ T)) -∗
    subsume (l ◁ₗ{β} uninit ly1) (l ◁ₗ{β} uninit ly2) T.
  Proof. unfold CanSolve in *. iIntros "[% [Hl2 $]] Hl". by iApply (merge_uninit with "Hl"). Qed.
  Global Instance subsume_uninit_merge_inst l β ly1 ly2 `{!CanSolve (ly1.(ly_size) ≤ ly2.(ly_size))%nat} :
    SubsumePlace l β (uninit ly1) (uninit ly2) | 20 :=
    λ T, i2p (subsume_uninit_merge l β ly1 ly2 T).

  Lemma type_return {B} Q e fn ls (fr : B → _):
    typed_val_expr e (λ v ty, v ◁ᵥ ty -∗ ∃ x, v ◁ᵥ (fr x).(fr_rty) ∗
    foldr (λ (e : (loc * layout)) T, e.1 ◁ₗ uninit e.2 ∗ T)
    ((fr x).(fr_R) ∗ True) (* ∗ True is for automation *)
    (zip ls (fn.(f_args) ++ fn.(f_local_vars)).*2)) -∗
    typed_stmt (Return e) fn ls fr Q.
  Proof.
    iIntros "He". iIntros (Hls).
    wps_bind. iApply "He". iIntros (v ty) "Hv HR".
    iApply wps_return.
    iDestruct ("HR" with "Hv") as (x) "[? HR]". iExists _. iFrame.
    move: Hls. move: (f_args fn ++ f_local_vars fn) => lys {fn} Hlys.
    iInduction ls as [|l ls] "IH" forall (lys Hlys);
      destruct lys as [|ly lys]=> //; csimpl in *; simplify_eq.
    1: rewrite right_id; by iFrame.
    iDestruct "HR" as "[Hl HR]". iFrame.
    iDestruct ("IH" with "[//] HR") as "[$ $]".
  Qed.


  Lemma type_add_uninit v2 β ly (p : loc) n it T:
    (⌜n ∈ it⌝ -∗ ⌜0 ≤ n⌝ ∗ ⌜Z.to_nat n ≤ ly.(ly_size)⌝%nat ∗ (
        p ◁ₗ{β} uninit (ly_set_size ly (Z.to_nat n)) -∗ v2 ◁ᵥ n @ int it -∗
          T (val_of_loc (p +ₗ n)) (t2mt ((p +ₗ n) @ &frac{β} (uninit (ly_offset ly (Z.to_nat n))))))) -∗
      typed_bin_op v2 (v2 ◁ᵥ n @ int it) p (p ◁ₗ{β} uninit ly) (PtrOffsetOp u8) (IntOp it) PtrOp T.
  Proof.
    iIntros "HT" (Hint) "Hp". iIntros (Φ) "HΦ".
    move: (Hint) => /val_of_int_in_range?.
    iDestruct ("HT" with "[//]") as (??) "HT".
    iDestruct (split_uninit (Z.to_nat n) with "Hp") as "[H1 H2]"; [lia..|].
    iApply wp_ptr_offset. by apply val_to_of_loc. by apply val_to_of_int. done.
    iModIntro. rewrite offset_loc_sz1//.
    iApply ("HΦ" with "[H2]"). 2: iApply ("HT" with "H1 []"). rewrite Z2Nat.id; [|lia]. by iFrame.
    by iPureIntro.
  Qed.
  Global Instance type_add_uninit_inst v2 β ly (p : loc) n it:
    TypedBinOp v2 (v2 ◁ᵥ n @ int it)%I p (p ◁ₗ{β} uninit ly) (PtrOffsetOp u8) (IntOp it) PtrOp :=
    λ T, i2p (type_add_uninit v2 β ly p n it T).

  Lemma annot_to_uninit l ty T `{!Movable ty}:
    (∀ v, v ◁ᵥ ty -∗ l ◁ₗ uninit ty.(ty_layout) -∗ T) -∗
    typed_annot_stmt ToUninit l (l ◁ₗ ty) T.
  Proof.
    iIntros "HT Hl". iApply step_fupd_intro => //. iModIntro.
    iDestruct (ty_aligned with "Hl") as %?.
    iDestruct (ty_deref with "Hl") as (v) "[Hmt Hv]".
    iDestruct (ty_size_eq with "Hv") as %?.
    iApply ("HT" with "Hv").
    iExists _. by iFrame.
  Qed.
  Global Instance annot_to_uninit_inst l ty `{!Movable ty}:
    TypedAnnotStmt (ToUninit) l (l ◁ₗ ty) :=
    λ T, i2p (annot_to_uninit l ty T).

End uninit.
Notation "uninit< ly >" := (uninit ly) (only printing, format "'uninit<' ly '>'") : printing_sugar.

Hint Extern 5 (SubsumePlace _ Own _ (uninit _)) =>
  unshelve notypeclasses refine (uninit_mono_inst _ _ _ ) : typeclass_instances.

Section void.
  Context `{!typeG Σ}.

  Definition void : type := uninit void_layout.

  Lemma type_void T:
    T (t2mt void) -∗ typed_value VOID T.
  Proof. iIntros "HT". iExists _. by iFrame. Qed.

  Global Instance type_void_inst : TypedValue VOID :=
    λ T, i2p (type_void T).

End void.
