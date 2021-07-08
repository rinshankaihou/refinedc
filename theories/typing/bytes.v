From refinedc.typing Require Export type.
From refinedc.typing Require Import programs int own.
Set Default Proof Using "Type".

(* NOTE: we might want to have a type [bytes : list mbyte → type] one day,
and the [bytewise] abstraction could be encoded on top of it. *)

Section bytewise.
  Context `{!typeG Σ}.
  Implicit Types P : mbyte → Prop.

  Program Definition bytewise (P : mbyte → Prop) (ly : layout) : type := {|
    ty_own β l :=
      ∃ v, ⌜v `has_layout_val` ly⌝ ∗
           ⌜l `has_layout_loc` ly⌝ ∗
           ⌜Forall P v⌝ ∗
           l ↦[β] v;
  |}%I.
  Next Obligation.
    iIntros (?????). iDestruct 1 as (?) "(?&?&?&Hl)".
    iMod (heap_mapsto_own_state_share with "Hl") as "Hl".
    eauto with iFrame.
  Qed.

  Global Program Instance movable_bytewise ly P : Movable (bytewise P ly) := {|
    ty_has_layout ly' := ly' = ly;
    ty_own_val v := ⌜v `has_layout_val` ly⌝ ∗ ⌜Forall P v⌝;
  |}%I.
  Next Obligation. iIntros (????->). by iDestruct 1 as (????) "_". Qed.
  Next Obligation. by iIntros (????-> [??]). Qed.
  Next Obligation. iIntros (????->). iDestruct 1 as (????) "?". by eauto. Qed.
  Next Obligation. iIntros (???? v -> ?) "? [%%]". iExists v. by iFrame. Qed.

  Lemma bytewise_weaken l β P1 P2 ly:
    (∀ b, P1 b → P2 b) →
    l ◁ₗ{β} bytewise P1 ly -∗ l ◁ₗ{β} bytewise P2 ly.
  Proof.
    iIntros (?). iDestruct 1 as (????) "H". iExists _; iFrame.
    iPureIntro; split_and! => //. by eapply Forall_impl.
  Qed.

  Lemma split_bytewise n l β P ly:
    (n ≤ ly.(ly_size))%nat →
    l ◁ₗ{β} bytewise P ly -∗
      l ◁ₗ{β} bytewise P (ly_set_size ly n) ∗
      (l +ₗ n) ◁ₗ{β} bytewise P (ly_offset ly n).
  Proof.
    iIntros (?). iDestruct 1 as (v Hv Hl HP) "Hl".
    rewrite -[v](take_drop n) heap_mapsto_own_state_app.
    iDestruct "Hl" as "[Hl1 Hl2]". iSplitL "Hl1".
    - iExists _. iFrame.
      eapply Forall_take in HP. rewrite /has_layout_val in Hv.
      by rewrite /has_layout_val take_length min_l // Hv.
    - rewrite take_length_le ?Hv //. iExists _. iFrame.
      eapply Forall_drop in HP. eapply has_layout_ly_offset in Hl.
      by rewrite /has_layout_val drop_length Hv.
  Qed.

  Lemma merge_bytewise l β P ly1 ly2:
    (ly1.(ly_size) ≤ ly2.(ly_size))%nat →
    (ly_align ly2 ≤ ly_align ly1)%nat →
    l ◁ₗ{β} bytewise P ly1 -∗
    (l +ₗ ly1.(ly_size)) ◁ₗ{β} (bytewise P (ly_offset ly2 ly1.(ly_size))) -∗
      l ◁ₗ{β} bytewise P ly2.
  Proof.
    iIntros (??).
    iDestruct 1 as (v1 Hv1 Hl1 HP1) "Hl1".
    iDestruct 1 as (v2 Hv2 Hl2 HP2) "Hl2".
    iExists (v1 ++ v2).
    rewrite heap_mapsto_own_state_app Hv1 /has_layout_val app_length Hv1 Hv2.
    iFrame. iPureIntro. split_and!.
    - rewrite {2}/ly_size/=. lia.
    - by apply: has_layout_loc_trans'.
    - by apply Forall_app.
  Qed.

  Lemma bytewise_loc_in_bounds l β P ly:
    l ◁ₗ{β} bytewise P ly -∗ loc_in_bounds l (ly_size ly).
  Proof.
    iDestruct 1 as (v <-) "(_&_&?)".
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.

  Global Instance loc_in_bounds_bytewise β P ly:
    LocInBounds (bytewise P ly) β (ly_size ly).
  Proof. constructor. iIntros (?). by iApply bytewise_loc_in_bounds. Qed.

  Lemma subsume_bytewise_eq l β P1 P2 ly1 ly2
        `{!CanSolve (ly1.(ly_size) = ly2.(ly_size))} T:
    ⌜∀ b, P1 b → P2 b⌝ ∗
    (⌜l `has_layout_loc` ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗ T) -∗
      subsume (l ◁ₗ{β} bytewise P1 ly1) (l ◁ₗ{β} bytewise P2 ly2) T.
  Proof.
    revert select (CanSolve _) => Hsz. unfold CanSolve in *.
    iDestruct 1 as (HPs) "HT". iDestruct 1 as (??? HP) "?".
    apply (Forall_impl _ _ _ HP) in HPs.
    iDestruct ("HT" with "[//]") as (?) "$".
    iExists _. iFrame. by rewrite /has_layout_val -Hsz.
  Qed.
  Global Instance subsume_bytewise_eq_inst l β P1 P2 ly1 ly2
        `{!CanSolve (ly1.(ly_size) = ly2.(ly_size))}:
    SubsumePlace l β (bytewise P1 ly1) (bytewise P2 ly2) | 10 :=
    λ T, i2p (subsume_bytewise_eq l β P1 P2 ly1 ly2 T).

  Lemma subsume_bytewise_merge l β P1 P2 ly1 ly2
        `{!CanSolve (ly1.(ly_size) ≤ ly2.(ly_size))%nat} T:
    ⌜∀ b, P1 b → P2 b⌝ ∗
    ⌜ly_align ly2 ≤ ly_align ly1⌝%nat ∗
    ((l +ₗ ly1.(ly_size)) ◁ₗ{β} bytewise P2 (ly_offset ly2 ly1.(ly_size)) ∗ T) -∗
    subsume (l ◁ₗ{β} bytewise P1 ly1) (l ◁ₗ{β} bytewise P2 ly2) T.
  Proof.
    unfold CanSolve in *.
    iIntros "(%&%&?&$) Hl".
    iDestruct (bytewise_weaken with "Hl") as "Hl" => //.
    iApply (merge_bytewise with "Hl") => //.
  Qed.
  Global Instance subsume_bytewise_merge_inst l β P1 P2 ly1 ly2
        `{!CanSolve (ly1.(ly_size) ≤ ly2.(ly_size))%nat}:
    SubsumePlace l β (bytewise P1 ly1) (bytewise P2 ly2) | 20 :=
    λ T, i2p (subsume_bytewise_merge l β P1 P2 ly1 ly2 T).

  Lemma subsume_bytewise_split l β P1 P2 ly1 ly2
        `{!CanSolve (ly2.(ly_size) ≤ ly1.(ly_size))%nat} T:
    ⌜∀ b, P1 b → P2 b⌝ ∗
    ⌜ly_align ly2 ≤ ly_align ly1⌝%nat ∗
    ((l +ₗ ly2.(ly_size)) ◁ₗ{β} bytewise P1 (ly_offset ly1 ly2.(ly_size)) -∗ T) -∗
    subsume (l ◁ₗ{β} bytewise P1 ly1) (l ◁ₗ{β} bytewise P2 ly2) T.
  Proof.
    unfold CanSolve in *.
    iIntros "(%&%&HT) Hl".
    iDestruct (split_bytewise with "Hl") as "[Hl1 Hl2]" => //.
    iDestruct (bytewise_weaken with "Hl1") as "Hl1" => //.
    iDestruct ("HT" with "Hl2") as "$".
    iDestruct "Hl1" as (????) "Hl1".
    iExists _; iFrame. iPureIntro; split_and! => //.
    by apply: has_layout_loc_trans'.
  Qed.
  Global Instance subsume_bytewise_split_inst l β P1 P2 ly1 ly2
        `{!CanSolve (ly2.(ly_size) ≤ ly1.(ly_size))%nat}:
    SubsumePlace l β (bytewise P1 ly1) (bytewise P2 ly2) | 15 :=
    λ T, i2p (subsume_bytewise_split l β P1 P2 ly1 ly2 T).

  Lemma type_add_bytewise v2 β P ly (p : loc) n it T:
    (⌜n ∈ it⌝ -∗
      ⌜0 ≤ n⌝ ∗
      ⌜Z.to_nat n ≤ ly.(ly_size)⌝%nat ∗
      (p ◁ₗ{β} bytewise P (ly_set_size ly (Z.to_nat n)) -∗ v2 ◁ᵥ n @ int it -∗
       T (val_of_loc (p +ₗ n)) (t2mt ((p +ₗ n) @ &frac{β} (bytewise P (ly_offset ly (Z.to_nat n))))))) -∗
    typed_bin_op v2 (v2 ◁ᵥ n @ int it) p (p ◁ₗ{β} bytewise P ly) (PtrOffsetOp u8) (IntOp it) PtrOp T.
  Proof.
    iIntros "HT" (Hint) "Hp". iIntros (Φ) "HΦ".
    move: (Hint) => /val_to_Z_in_range?.
    iDestruct ("HT" with "[//]") as (??) "HT".
    iDestruct (split_bytewise (Z.to_nat n) with "Hp") as "[H1 H2]"; [lia..|].
    rewrite -!(offset_loc_sz1 u8)// Z2Nat.id; [|lia].
    iDestruct (loc_in_bounds_in_bounds with "H2") as "#?".
    iApply wp_ptr_offset; [ by apply val_to_of_loc | done | |].
    { iApply loc_in_bounds_shorten; [|done]; lia. }
    iModIntro. iApply ("HΦ" with "[H2]"). 2: iApply ("HT" with "H1 []").
    - by iFrame.
    - by iPureIntro.
  Qed.
  Global Instance type_add_bytewise_inst v2 β P ly (p : loc) n it:
    TypedBinOp v2 (v2 ◁ᵥ n @ int it)%I p (p ◁ₗ{β} bytewise P ly) (PtrOffsetOp u8) (IntOp it) PtrOp :=
    λ T, i2p (type_add_bytewise v2 β P ly p n it T).
End bytewise.

Notation "bytewise< P , ly >" := (bytewise P ly)
  (only printing, format "'bytewise<' P ',' ly '>'") : printing_sugar.

Typeclasses Opaque bytewise.

Notation uninit := (bytewise (λ _, True)).

Section uninit.
  Context `{!typeG Σ}.

  Lemma uninit_own_spec l ly:
    (l ◁ₗ uninit ly)%I ≡ (l ↦|ly|)%I.
  Proof.
    rewrite /ty_own/=; iSplit.
    - iDestruct 1 as (??? _) "Hl". iExists _; by iFrame.
    - iDestruct 1 as (v ??) "Hl". iExists v; iFrame. by rewrite Forall_forall.
  Qed.

  (* This only works for [Own] since [ty] might have interior mutability. *)
  Lemma uninit_mono l ty ly `{!Movable ty} `{!CanSolve (ty.(ty_has_layout) ly)} T:
    (∀ v, v ◁ᵥ ty -∗ T) -∗
    subsume (l ◁ₗ ty) (l ◁ₗ uninit ly) T.
  Proof.
    unfold CanSolve in *; subst. iIntros "HT Hl".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iSplitL "Hl".
    - iExists v. iFrame. by rewrite Forall_forall.
    - by iApply "HT".
  Qed.
  (* This rule is handled with a definition and an [Hint Extern] (not
  with an instance) since [Movable] is a dependent subgoal (used by
  [ty.(ty_has_layout)] in the [CanSolve] instance), and it is thus
  shelved according to heuristics used by Coq. We thus use [unshleve]
  in the [Hint Extern] to prevent that.

  Also this rule should only apply ty is not uninit as this case is
  covered by the rules for bytes and the CanSolve can be quite
  expensive. *)
  Definition uninit_mono_inst l ty ly `{!Movable ty} `{!CanSolve (ty.(ty_has_layout) ly)}:
    SubsumePlace l Own ty (uninit ly) :=
    λ T, i2p (uninit_mono l ty ly T).

  (* Typing rule for [Return] (used in [theories/typing/automation.v]). *)
  Lemma type_return Q e fn ls R:
    typed_val_expr e (λ v ty,
      foldr (λ (e : (loc * layout)) T, e.1 ◁ₗ uninit e.2 ∗ T)
      (R v ty)
      (zip ls (fn.(f_args) ++ fn.(f_local_vars)).*2)) -∗
    typed_stmt (Return e) fn ls R Q.
  Proof.
    iIntros "He" (Hls). wps_bind. iApply "He".
    iIntros (v ty) "Hv HR". iApply wps_return.
    rewrite /typed_stmt_post_cond. move: Hls. move: (f_args fn ++ f_local_vars fn) => lys {fn} Hlys.
    iInduction ls as [|l ls] "IH" forall (lys Hlys); destruct lys as [|ly lys]=> //; csimpl in *; simplify_eq.
    { iExists _. iFrame. }
    iDestruct "HR" as "[Hl HR]".
    iDestruct ("IH" with "[//] Hv HR") as (ty') "[?[??]]".
    iExists _. iFrame.
    rewrite /ty_own/=. iDestruct "Hl" as (????) "Hl".
    iExists _. by iFrame.
  Qed.
End uninit.

Notation "uninit< ly >" := (uninit ly) (only printing, format "'uninit<' ly '>'") : printing_sugar.

(* See the definition of [uninit_mono_inst].
   This hint should only apply ty is not uninit as this case is covered by the rules for bytes. *)
Hint Extern 5 (SubsumePlace _ Own ?ty (uninit _)) =>
  lazymatch ty with
  | uninit _ => fail
  | _ => unshelve notypeclasses refine (uninit_mono_inst _ _ _)
  end
  : typeclass_instances.

Section void.
  Context `{!typeG Σ}.

  Definition void : type := uninit void_layout.

  Lemma type_void T:
    T (t2mt void) -∗ typed_value VOID T.
  Proof. iIntros "HT". rewrite /VOID. iExists _. by iFrame. Qed.
  Global Instance type_void_inst : TypedValue VOID :=
    λ T, i2p (type_void T).
End void.

Notation zeroed := (bytewise (λ b, b = MByte byte0 None)).

Section zeroed.
  Context `{!typeG Σ}.

  Lemma subsume_uninit_zeroed p ly1 ly2 T:
    ⌜ly_align ly1 = ly_align ly2⌝ ∗ ⌜ly_size ly2 = 0%nat⌝ ∗ (p ◁ₗ uninit ly1 -∗ T) -∗
    subsume (p ◁ₗ uninit ly1)%I (p ◁ₗ zeroed ly2)%I T.
  Proof.
    iDestruct 1 as (H1 H2) "HT". iIntros "Hp".
    iDestruct (ty_aligned with "Hp") as %Hal; [done|].
    iDestruct (loc_in_bounds_in_bounds with "Hp") as "#Hlib".
    iSplitR; last by iApply "HT".
    iExists []. rewrite Forall_nil /has_layout_loc -H1. repeat iSplit => //.
    rewrite /heap_mapsto_own_state heap_mapsto_eq /heap_mapsto_def /=.
    iSplit => //. iApply (loc_in_bounds_shorten with "Hlib"). lia.
  Qed.
  Global Instance subsume_uninit_zeroed_0_inst p ly1 ly2:
    Subsume (p ◁ₗ uninit ly1)%I (p ◁ₗ zeroed ly2)%I :=
    λ T, i2p (subsume_uninit_zeroed p ly1 ly2 T).
End zeroed.
Notation "zeroed< ly >" := (zeroed ly)
  (only printing, format "'zeroed<' ly '>'") : printing_sugar.
