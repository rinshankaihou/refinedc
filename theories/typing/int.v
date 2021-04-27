From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section int.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition int_inner_type (it : int_type) (n : Z) : type := {|
    ty_own β l := ∃ v, ⌜val_to_Z_weak v it = Some n⌝ ∗ ⌜l `has_layout_loc` it⌝ ∗ l ↦[β] v;
  |}%I.
  Next Obligation.
    iIntros (it n l ??) "(%v&%Hv&%Hl&H)". iExists v.
    do 2 (iSplitR; first done). by iApply heap_mapsto_own_state_share.
  Qed.

  Program Definition int (it : int_type) : rtype := {|
    rty_type := Z;
    rty := int_inner_type it;
  |}.

  Global Program Instance rmovable_int it : RMovable (int it) := {|
    rmovable n := {|
      ty_layout := it_layout it;
      ty_own_val v := ⌜val_to_Z_weak v it = Some n⌝;
    |}
  |}%I.
  Next Obligation. iIntros (???) "(%&%&$&_)". Qed.
  Next Obligation. iIntros (??? H) "!%". by apply val_to_Z_weak_length in H. Qed.
  Next Obligation. iIntros (???) "(%v&%&%&Hl)". eauto with iFrame. Qed.
  Next Obligation. iIntros (??? v ?) "Hl %". iExists v. eauto with iFrame. Qed.
  Next Obligation. iIntros (???). done. Qed.

  Lemma int_loc_in_bounds l β n it:
     l ◁ₗ{β} n @ int it -∗ loc_in_bounds l (bytes_per_int it).
  Proof.
    iIntros "(%&%Hv&%&Hl)". move: Hv => /val_to_Z_weak_length <-.
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.

  Global Instance loc_in_bounds_int n it β: LocInBounds (n @ int it) β (bytes_per_int it).
  Proof.
    constructor. iIntros (l) "Hl".
    iDestruct (int_loc_in_bounds with "Hl") as "Hlib".
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.

  Lemma ty_own_int_in_range l β n it : l ◁ₗ{β} n @ int it -∗ ⌜n ∈ it⌝.
  Proof.
    iIntros "Hl". destruct β.
    - iDestruct (ty_deref with "Hl") as (?) "[_ %]".
      iPureIntro. by eapply val_to_Z_weak_in_range.
    - iDestruct "Hl" as (?) "[% _]".
      iPureIntro. by eapply val_to_Z_weak_in_range.
  Qed.

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance int_copyable x it : Copyable (x @ int it).
  Next Obligation.
    iIntros (?????) "(%v&%Hv&%Hl&Hl)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iSplitR => //. iExists q, v. iFrame. iModIntro. eauto with iFrame.
  Qed.

  Global Instance int_timeless l z it:
    Timeless (l ◁ₗ z @ int it)%I.
  Proof. apply _. Qed.

End int.
(* Typeclasses Opaque int. *)
Notation "int< it >" := (int it) (only printing, format "'int<' it '>'") : printing_sugar.

(* TODO: move this to an extra file? *)
Section boolean.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition boolean_inner_type (it : int_type) (b : bool) : type :=
    (Z_of_bool b) @ int it.

  Program Definition boolean (it : int_type) : rtype := {|
    rty_type := bool;
    rty := boolean_inner_type it;
  |}.

  Global Program Instance rmovable_boolean it : RMovable (boolean it) := {|
    rmovable b := (rmovable (int it)) (Z_of_bool b);
  |}.
  Next Obligation. iIntros (???). done. Qed.

  Lemma boolean_own_val_eq v b it:
    (v ◁ᵥ b @ boolean it)%I ≡ ⌜val_to_Z_weak v it = Some (Z_of_bool b)⌝%I.
  Proof. done. Qed.

  Global Instance boolean_timeless l b it:
    Timeless (l ◁ₗ b @ boolean it)%I.
  Proof. apply _. Qed.

End boolean.
Notation "boolean< it >" := (boolean it) (only printing, format "'boolean<' it '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ}.

  (*** int *)
  Lemma type_val_int n it T:
    ⌜n ∈ it⌝ ∗ T (t2mt (n @ (int it))) -∗ typed_value (i2v n it) T.
  Proof.
    iIntros "[%Hn HT]".
    move: Hn => /val_of_Z_is_Some [v Hv].
    move: (Hv) => /val_to_of_Z Hn.
    iExists _. iFrame. iPureIntro.
    rewrite /i2v Hv /=. by apply val_to_Z_to_int_repr_Z.
  Qed.
  Global Instance type_val_int_inst n it : TypedValue (i2v n it) :=
    λ T, i2p (type_val_int n it T).

  (* TODO: instead of adding it_in_range to the context here, have a
  SimplifyPlace/Val instance for int which adds it to the context if
  it does not yet exist (using check_hyp_not_exists)?! *)
  Lemma type_relop_int_int it v1 n1 v2 n2 T b op:
    match op with
    | EqOp => Some (bool_decide (n1 = n2))
    | NeOp => Some (bool_decide (n1 ≠ n2))
    | LtOp => Some (bool_decide (n1 < n2))
    | GtOp => Some (bool_decide (n1 > n2))
    | LeOp => Some (bool_decide (n1 <= n2))
    | GeOp => Some (bool_decide (n1 >= n2))
    | _ => None
    end = Some b →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ T (i2v (Z_of_bool b) i32) (t2mt (b @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT %Hv1 %Hv2 %Φ HΦ".
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_to_Z_weak_in_range.
    iApply (wp_binop_det (i2v (Z_of_bool b) i32)). iSplit.
    { iIntros (??) "_ !%". split; last (move => ->; by econstructor).
      destruct op => //; inversion 1; by simplify_eq. }
    iIntros "!>". iApply "HΦ" => //. by destruct b.
  Qed.

  Global Program Instance type_eq_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ (int it))%I v2 (n2 @ (int it))%I EqOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int it v1 n1 v2 n2 T (bool_decide (n1 = n2)) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_ne_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ (int it))%I v2 (n2 @ (int it))%I NeOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int it v1 n1 v2 n2 T (bool_decide (n1 ≠ n2)) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_lt_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ (int it))%I v2 (n2 @ (int it))%I LtOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int it v1 n1 v2 n2 T (bool_decide (n1 < n2)) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_gt_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ (int it))%I v2 (n2 @ (int it))%I GtOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int it v1 n1 v2 n2 T (bool_decide (n1 > n2)) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_le_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ (int it))%I v2 (n2 @ (int it))%I LeOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int it v1 n1 v2 n2 T (bool_decide (n1 <= n2)) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_ge_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ (int it))%I v2 (n2 @ (int it))%I GeOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int it v1 n1 v2 n2 T (bool_decide (n1 >= n2)) _ _).
  Next Obligation. done. Qed.

  Definition arith_op_result (it : int_type) n1 n2 op : option Z :=
    match op with
    | AddOp => Some (n1 + n2)
    | SubOp => Some (n1 - n2)
    | MulOp => Some (n1 * n2)
    | AndOp => Some (Z.land n1 n2)
    | OrOp  => Some (Z.lor n1 n2)
    | XorOp => Some (Z.lxor n1 n2)
    | ShlOp => Some (n1 ≪ n2)
    | ShrOp => Some (n1 ≫ n2)
    | DivOp => Some (n1 `quot` n2)
    | ModOp => Some (n1 `rem` n2)
    | _     => None (* Relational operators. *)
    end.

  Definition arith_op_sidecond (it : int_type) (n1 n2 n : Z) op : Prop :=
    match op with
    | AddOp => n ∈ it
    | SubOp => n ∈ it
    | MulOp => n ∈ it
    | AndOp => True
    | OrOp  => True
    | XorOp => True
    | ShlOp => 0 ≤ n2 < bits_per_int it ∧ 0 ≤ n1 ∧ n ≤ max_int it
    | ShrOp => 0 ≤ n2 < bits_per_int it ∧ 0 ≤ n1 (* Result of shifting negative numbers is implementation defined. *)
    | DivOp => n2 ≠ 0 ∧ n ∈ it
    | ModOp => n2 ≠ 0 ∧ n ∈ it
    | _     => True (* Relational operators. *)
    end.

  Lemma bitwise_op_result_in_range op bop (it : int_type) n1 n2 :
    (0 ≤ n1 → 0 ≤ n2 → 0 ≤ op n1 n2) →
    bool_decide (op n1 n2 < 0) = bop (bool_decide (n1 < 0)) (bool_decide (n2 < 0)) →
    (∀ k, Z.testbit (op n1 n2) k = bop (Z.testbit n1 k) (Z.testbit n2 k)) →
    n1 ∈ it → n2 ∈ it → op n1 n2 ∈ it.
  Proof.
    move => Hnonneg Hsign Htestbit.
    rewrite /elem_of /int_elem_of_it /min_int /max_int.
    destruct (it_signed it).
    - rewrite /int_half_modulus.
      move ? : (bits_per_int it - 1) => k.
      have ? : 0 ≤ k.
      { suff : bits_per_int it > 0 by lia. by apply: bits_per_int_gt_0. }
      have Hb : ∀ n, -2^k ≤ n ≤ 2^k - 1 ↔
        ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0)
        by intros; rewrite -bounded_iff_bits; lia.
      move => /Hb Hn1 /Hb Hn2.
      apply Hb => l Hl.
      by rewrite Htestbit Hsign Hn1 ?Hn2.
    - rewrite /int_modulus.
      move ? : (bits_per_int it) => k.
      have ? : 0 ≤ k.
      { suff : bits_per_int it > 0 by lia. by apply: bits_per_int_gt_0. }
      have Hb : ∀ n, 0 ≤ n → n ≤ 2^k - 1 ↔
        ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0)
        by intros; rewrite bool_decide_false -?pos_bounded_iff_bits; lia.
      move => [Hn1 /Hb HN1] [Hn2 /Hb HN2].
      have Hn := Hnonneg Hn1 Hn2.
      split; first done.
      apply (Hb _ Hn) => l Hl.
      by rewrite Htestbit HN1 ?HN2.
  Qed.

  Lemma arith_op_result_in_range (it : int_type) (n1 n2 n : Z) op :
    n1 ∈ it → n2 ∈ it → arith_op_result it n1 n2 op = Some n →
    arith_op_sidecond it n1 n2 n op → n ∈ it.
  Proof.
    move => Hn1 Hn2 Hn Hsc.
    destruct op => //=; simpl in Hsc, Hn; destruct_and? => //.
    all: inversion Hn; simplify_eq.
    - apply (bitwise_op_result_in_range Z.land andb) => //.
      + rewrite Z.land_nonneg; naive_solver.
      + repeat case_bool_decide; try rewrite -> Z.land_neg in *; naive_solver.
      + by apply Z.land_spec.
    - apply (bitwise_op_result_in_range Z.lor orb) => //.
      + by rewrite Z.lor_nonneg.
      + repeat case_bool_decide; try rewrite -> Z.lor_neg in *; naive_solver.
      + by apply Z.lor_spec.
    - apply (bitwise_op_result_in_range Z.lxor xorb) => //.
      + by rewrite Z.lxor_nonneg.
      + have Hn : ∀ n, bool_decide (n < 0) = negb (bool_decide (0 ≤ n)).
        { intros. repeat case_bool_decide => //; lia. }
        rewrite !Hn.
        repeat case_bool_decide; try rewrite -> Z.lxor_nonneg in *; naive_solver.
      + by apply Z.lxor_spec.
    - split.
      + trans 0; [ apply min_int_le_0 | by apply Z.shiftl_nonneg ].
      + done.
    - split.
      + trans 0; [ apply min_int_le_0 | by apply Z.shiftr_nonneg ].
      + destruct Hn1.
        trans n1; last done. rewrite Z.shiftr_div_pow2; last by lia.
        apply Z.div_le_upper_bound. { apply Z.pow_pos_nonneg => //. }
        rewrite -[X in X ≤ _]Z.mul_1_l. apply Z.mul_le_mono_nonneg_r => //.
        rewrite -(Z.pow_0_r 2). apply Z.pow_le_mono_r; lia.
  Qed.

  Lemma type_arithop_int_int it v1 n1 v2 n2 T n op:
    arith_op_result it n1 n2 op = Some n →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜arith_op_sidecond it n1 n2 n op⌝ ∗ T (i2v n it) (t2mt (n @ int it))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT %Hv1 %Hv2 %Φ HΦ".
    iDestruct ("HT" with "[] []" ) as (Hsc) "HT".
    1-2: iPureIntro; by apply: val_to_Z_weak_in_range.
    assert (n ∈ it) as [v Hv]%val_of_Z_is_Some.
    { apply: arith_op_result_in_range => //; by apply: val_to_Z_weak_in_range. }
    move: (Hv) => /val_of_Z_in_range ?. rewrite /i2v Hv /=.
    iApply (wp_binop_det v). iSplit.
    - iIntros (??) "_ !%". split.
      + destruct op => //.
        all: inversion 1; simplify_eq/=.
        all: try case_bool_decide => //.
        all: destruct it as [? []]; simplify_eq/= => //.
        all: try by rewrite ->it_in_range_mod in * => //; simplify_eq.
      + move => ->; destruct op => //; econstructor => // => //.
        all: try by inversion Hsc; case_bool_decide; naive_solver.
        all: destruct it as [? []]; simplify_eq/= => //.
        all: try by rewrite it_in_range_mod.
    - iIntros "!>". iApply "HΦ"; last done. iPureIntro.
      apply val_to_of_Z in Hv. by apply val_to_Z_to_int_repr_Z.
  Qed.
  Global Program Instance type_add_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I AddOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 + n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_sub_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I SubOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 - n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_mul_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I MulOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 * n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_div_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I DivOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 `quot` n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_mod_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I ModOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 `rem` n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_and_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I AndOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (Z.land n1 n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_or_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I OrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (Z.lor n1 n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_xor_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I XorOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (Z.lxor n1 n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shl_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I ShlOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 ≪ n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shr_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I ShrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int it v1 n1 v2 n2 T (n1 ≫ n2) _ _).
  Next Obligation. done. Qed.

  Inductive destruct_hint_if_int :=
  | DestructHintIfInt (n : Z).

  Lemma type_if_int it n v T1 T2:
    destruct_hint (DHintDecide (n ≠ 0)) (DestructHintIfInt n)
    (if decide (n ≠ 0) then T1 else T2) -∗
    typed_if (IntOp it) v (n @ int it) T1 T2.
  Proof.
    unfold destruct_hint. iIntros "Hs %Hb" => /=.
    iExists it, n. iSplit; first done. iSplit; first done.
    by do !case_decide.
  Qed.
  Global Instance type_if_int_inst n v it : TypedIf (IntOp it) v (n @ int it) :=
    λ T1 T2, i2p (type_if_int it n v T1 T2).

  Inductive destruct_hint_switch_int :=
  | DestructHintSwitchIntCase (n : Z)
  | DestructHintSwitchIntDefault.

  Lemma type_switch_int {B} n it m ss def Q fn ls (fr : B → _) v:
    ([∧ map] i↦mi ∈ m, destruct_hint DHintInfo (DestructHintSwitchIntCase i) (
             ⌜n = i⌝ -∗ ∃ s, ⌜ss !! mi = Some s⌝ ∗ typed_stmt s fn ls fr Q)) ∧
    (destruct_hint DHintInfo (DestructHintSwitchIntDefault) (
                     ⌜n ∉ (map_to_list m).*1⌝ -∗ typed_stmt def fn ls fr Q)) -∗
    typed_switch v (n @ int it) it m ss def fn ls fr Q.
  Proof.
    unfold destruct_hint. iIntros "HT %Hv". iExists n. iSplit; first done.
    iInduction m as [] "IH" using map_ind; simplify_map_eq => //.
    { iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_empty. set_solver. }
    rewrite big_andM_insert //. destruct (decide (n = i)); subst.
    - rewrite lookup_insert. iDestruct "HT" as "[[HT _] _]". by iApply "HT".
    - rewrite lookup_insert_ne//. iApply "IH". iSplit; first by iDestruct "HT" as "[[_ HT] _]".
      iIntros (Hn). iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_insert //. set_solver.
  Qed.
  Global Instance type_switch_int_inst n v it : TypedSwitch v (n @ int it) it :=
    λ B m ss def fn ls fr Q, i2p (type_switch_int n it m ss def Q fn ls fr v).

  Lemma type_neg_int n it v T:
    (⌜n ∈ it⌝ -∗ ⌜it.(it_signed)⌝ ∗ ⌜n ≠ min_int it⌝ ∗ T (i2v (-n) it) (t2mt ((-n) @ int it))) -∗
    typed_un_op v (v ◁ᵥ n @ int it)%I (NegOp) (IntOp it) T.
  Proof.
    iIntros "HT %Hv %Φ HΦ". move: (Hv) => /val_to_Z_weak_in_range ?.
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    have Hmin_n : val_of_Z (- n) it = Some (i2v (- n) it). {
      have [|? Hv'] := val_of_Z_is_Some it (- n); last by rewrite /i2v Hv'.
      unfold elem_of, int_elem_of_it, max_int, min_int in *.
      destruct it as [?[]] => //; simpl in *; lia.
    }
    iApply wp_neg_int => //. iApply ("HΦ" with "[] HT").
    iPureIntro. apply val_to_of_Z in Hmin_n.
    by apply val_to_Z_to_int_repr_Z.
  Qed.
  Global Instance type_neg_int_inst n it v:
    TypedUnOpVal v (n @ int it)%I NegOp (IntOp it) :=
    λ T, i2p (type_neg_int n it v T).

  Lemma type_cast_int n it1 it2 v T:
    (⌜n ∈ it1⌝ -∗ ⌜n ∈ it2⌝ ∗ ∀ v, T v (t2mt (n @ int it2))) -∗
    typed_un_op v (v ◁ᵥ n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT %Hv %Φ HΦ".
    iDestruct ("HT" with "[]") as (Hin) "HT".
    { iPureIntro. by apply: val_to_Z_weak_in_range. }
    apply fmap_Some in Hv as [i [Hv ->]].
    move: (Hin) => /val_of_int_repr_is_Some [v' Hv'].
    move: (Hv') => /val_to_of_int_repr Hv''.
    iDestruct ("HT" $! v') as "HT".
    iApply wp_cast_int => //. iApply ("HΦ" with "[] HT") => //.
    iPureIntro. by rewrite /val_to_Z_weak Hv''.
  Qed.
  Global Instance type_cast_int_inst n it1 it2 v:
    TypedUnOpVal v (n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) :=
    λ T, i2p (type_cast_int n it1 it2 v T).

  Lemma type_not_int n1 it v1 T:
    let n := if it_signed it then Z.lnot n1 else Z_lunot (bits_per_int it) n1 in
    (⌜n1 ∈ it⌝ -∗ T (i2v n it) (t2mt (n @ int it))) -∗
    typed_un_op v1 (v1 ◁ᵥ n1 @ int it)%I (NotIntOp) (IntOp it) T.
  Proof.
    iIntros "%n HT %Hv1 %Φ HΦ".
    have Hn1: n1 ∈ it by apply: val_to_Z_weak_in_range.
    iDestruct ("HT" with "[//]") as "HT".
    have : n ∈ it.
    { move: Hn1.
      rewrite /n /elem_of /int_elem_of_it /min_int /max_int.
      destruct (it_signed it).
      - rewrite /int_half_modulus /Z.lnot. lia.
      - rewrite /int_modulus => ?.
        have -> : ∀ a b, a ≤ b - 1 ↔ a < b by lia.
        have ? := bits_per_int_gt_0 it.
        apply Z_lunot_range; lia. }
    rewrite /n => /val_of_Z_is_Some [v Hv]. rewrite /i2v Hv /=.
    iApply (wp_unop_det v). iSplit.
    - iIntros (σ v') "_ !%". split.
      + by inversion 1; simplify_eq.
      + move => ->. by econstructor.
    - iIntros "!>". iApply "HΦ"; last done. iPureIntro.
      apply val_to_of_Z in Hv. by apply val_to_Z_to_int_repr_Z.
  Qed.
  Global Instance type_not_int_inst n it v:
    TypedUnOpVal v (n @ int it)%I NotIntOp (IntOp it) :=
    λ T, i2p (type_not_int n it v T).

  (* TODO: replace this with a typed_cas once it is refactored to take E as an argument. *)
  Lemma wp_cas_suc_int it z1 z2 zd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 = z2 →
    l1 ◁ₗ z1 @ int it -∗ l2 ◁ₗ z2 @ int it -∗ vd ◁ᵥ zd @ int it -∗
    ▷ (l1 ◁ₗ zd @ int it -∗ l2 ◁ₗ z2 @ int it -∗ Φ (val_of_bool true)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? ->) "(%v1&%&%&Hl1) (%v2&%&%&Hl2) % HΦ/=".
    iApply (wp_cas_suc with "Hl1 Hl2") => //.
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by eapply val_to_Z_weak_length. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _; by iFrame.
  Qed.

  Lemma wp_cas_fail_int it z1 z2 zd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 ≠ z2 →
    l1 ◁ₗ z1 @ int it -∗ l2 ◁ₗ z2 @ int it -∗ vd ◁ᵥ zd @ int it -∗
    ▷ (l1 ◁ₗ z1 @ int it -∗ l2 ◁ₗ z1 @ int it -∗ Φ (val_of_bool false)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? ?) "(%v1&%&%&Hl1) (%v2&%&%&Hl2) % HΦ/=".
    iApply (wp_cas_fail with "Hl1 Hl2") => //.
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by eapply val_to_Z_weak_length. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _; by iFrame.
  Qed.

  (*** bool *)
  Lemma type_val_bool' b:
    ⊢ (val_of_bool b) ◁ᵥ (b @ boolean bool_it).
  Proof. iIntros. by destruct b. Qed.
  Lemma type_val_bool b T:
    (T (t2mt (b @ boolean bool_it))) -∗ typed_value (val_of_bool b) T.
  Proof. iIntros "HT". iExists _. iFrame. iApply type_val_bool'. Qed.
  Global Instance type_val_bool_inst b : TypedValue (val_of_bool b) :=
    λ T, i2p (type_val_bool b T).

  Inductive destruct_hint_if_bool :=
  | DestructHintIfBool (b : bool).

  Lemma type_relop_bool_bool it v1 b1 v2 b2 T b op:
    match op with
    | EqOp => Some (eqb b1 b2)
    | NeOp => Some (negb (eqb b1 b2))
    | _ => None
    end = Some b →
    (T (i2v (Z_of_bool b) i32) (t2mt (b @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ b1 @ boolean it) v2 (v2 ◁ᵥ b2 @ boolean it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT %Hv1 %Hv2 %Φ HΦ".
    iApply (wp_binop_det (i2v (Z_of_bool b) i32)). iSplit.
    { iIntros (??) "_ !%". destruct op, b1, b2; simplify_eq;
      (split; [ inversion 1 | move => -> ]); simplify_eq;
      econstructor => //; by case_bool_decide. }
    iApply "HΦ"; last done. iPureIntro. by destruct b.
  Qed.

  Global Program Instance type_eq_bool_bool_inst it v1 b1 v2 b2:
    TypedBinOpVal v1 (b1 @ (boolean it))%I v2 (b2 @ (boolean it))%I EqOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_bool_bool it v1 b1 v2 b2 T (eqb b1 b2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_ne_bool_bool_inst it v1 b1 v2 b2:
    TypedBinOpVal v1 (b1 @ (boolean it))%I v2 (b2 @ (boolean it))%I NeOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_bool_bool it v1 b1 v2 b2 T (negb (eqb b1 b2)) _ _).
  Next Obligation. done. Qed.

  Lemma type_if_bool it (b : bool) v T1 T2 :
    destruct_hint (DHintDestruct _ b) (DestructHintIfBool b)
    (if b then T1 else T2) -∗
    typed_if (IntOp it) v (b @ boolean it) T1 T2.
  Proof.
    unfold destruct_hint. iIntros "Hs %Hb".
    iExists _, _. do 2 iSplit => //. by destruct b.
  Qed.
  Global Instance type_if_bool_inst it b v : TypedIf (IntOp it) v (b @ boolean it) :=
    λ T1 T2, i2p (type_if_bool it b v T1 T2).

  Lemma type_assert_bool {B} (b : bool) s Q fn ls (fr : B → _) v :
    (⌜b⌝ ∗ typed_stmt s fn ls fr Q) -∗
    typed_assert v (b @ boolean bool_it) s fn ls fr Q.
  Proof.
    iIntros "[% Hs] %Hb". iExists _. iFrame. iSplit; first done. by destruct b.
  Qed.
  Global Instance type_assert_bool_inst b v : TypedAssert v (b @ boolean bool_it) :=
    λ B s fn ls fr Q, i2p (type_assert_bool _ _ _ _ _ _ _).

  Lemma type_cast_bool b it1 it2 v T:
    (∀ v, T v (t2mt (b @ boolean it2))) -∗
    typed_un_op v (v ◁ᵥ b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT %Hv %Φ HΦ".
    apply fmap_Some in Hv as [i [Hv Heq]].
    have Hin: (int_repr_to_Z i ∈ it2).
    { rewrite -Heq. apply Z_of_bool_elem_of_int_type. }
    move: (Hin) => /val_of_int_repr_is_Some [v' Hv'].
    move: (Hv') => /val_to_of_int_repr Hv''.
    iDestruct ("HT" $! v') as "HT".
    iApply wp_cast_int => //=. iApply ("HΦ" with "[] HT") => //.
    iPureIntro. by rewrite /val_to_Z_weak Hv'' Heq.
  Qed.
  Global Instance type_cast_bool_inst b it1 it2 v:
    TypedUnOpVal v (b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) :=
    λ T, i2p (type_cast_bool b it1 it2 v T).

  (* TODO: replace this with a typed_cas once it is refactored to take E as an argument. *)
  Lemma wp_cas_suc_bool it b1 b2 bd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    b1 = b2 →
    l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ vd ◁ᵥ bd @ boolean it -∗
    ▷ (l1 ◁ₗ bd @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ Φ (val_of_bool true)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof. iIntros (? ->) "Hl1 Hl2 Hv HΦ/=". iApply (wp_cas_suc_int with "Hl1 Hl2 Hv"); done. Qed.

  Lemma wp_cas_fail_bool it b1 b2 bd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    b1 ≠ b2 →
    l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ vd ◁ᵥ bd @ boolean it -∗
    ▷ (l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b1 @ boolean it -∗ Φ (val_of_bool false)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? ?) "Hl1 Hl2 Hv HΦ/=". iApply (wp_cas_fail_int with "Hl1 Hl2 Hv"); try done.
    by destruct b1, b2.
  Qed.


  (*** int <-> bool *)
  Lemma subsume_int_bool_place l β n b it T:
    ⌜n = Z_of_bool b⌝ ∗ T -∗
    subsume (l ◁ₗ{β} n @ int it) (l ◁ₗ{β} b @ boolean it) T.
  Proof. iIntros "[-> $] Hint". iDestruct "Hint" as (x Hx) "?". iExists _. by iFrame. Qed.
  Global Instance subsume_int_bool_place_inst l β n b it:
    SubsumePlace l β (n @ int it) (b @ boolean it) :=
    λ T, i2p (subsume_int_bool_place l β n b it T).

  Lemma subsume_int_bool_val v n b it T:
    ⌜n = Z_of_bool b⌝ ∗ T -∗
    subsume (v ◁ᵥ n @ int it) (v ◁ᵥ b @ boolean it) T.
  Proof. by iIntros "[-> $] %". Qed.
  Global Instance subsume_int_bool_val_inst v n b it:
    SubsumeVal v (n @ int it) (b @ boolean it) :=
    λ T, i2p (subsume_int_bool_val v n b it T).


  Lemma type_binop_bool_int it1 it2 it3 it4 v1 b1 v2 n2 T op:
    typed_bin_op v1 (v1 ◁ᵥ (Z_of_bool b1) @ int it1) v2 (v2 ◁ᵥ n2 @ int it2) op (IntOp it3) (IntOp it4) T -∗
    typed_bin_op v1 (v1 ◁ᵥ b1 @ boolean it1) v2 (v2 ◁ᵥ n2 @ int it2) op (IntOp it3) (IntOp it4) T.
  Proof. iIntros "HT". iApply "HT". Qed.
  Global Instance type_binop_bool_int_inst it1 it2 it3 it4 v1 b1 v2 n2 op:
    TypedBinOpVal v1 (b1 @ boolean it1)%I v2 (n2 @ int it2)%I op (IntOp it3) (IntOp it4) :=
    λ T, i2p (type_binop_bool_int it1 it2 it3 it4 v1 b1 v2 n2 T op).

  Lemma type_binop_int_bool it1 it2 it3 it4 v1 b1 v2 n2 T op:
    typed_bin_op v1 (v1 ◁ᵥ n2 @ int it2) v2 (v2 ◁ᵥ (Z_of_bool b1) @ int it1) op (IntOp it3) (IntOp it4) T -∗
    typed_bin_op v1 (v1 ◁ᵥ n2 @ int it2) v2 (v2 ◁ᵥ b1 @ boolean it1) op (IntOp it3) (IntOp it4) T.
  Proof. iIntros "HT". iApply "HT". Qed.
  Global Instance type_binop_int_bool_inst it1 it2 it3 it4 v1 b1 v2 n2 op:
    TypedBinOpVal v1 (n2 @ int it2)%I v2 (b1 @ boolean it1)%I op (IntOp it3) (IntOp it4) :=
    λ T, i2p (type_binop_int_bool it1 it2 it3 it4 v1 b1 v2 n2 T op).

End programs.
Typeclasses Opaque int_inner_type boolean_inner_type.

Notation "'if' p " := (DestructHintIfBool p) (at level 100, only printing).
Notation "'if' p ≠ 0 " := (DestructHintIfInt p) (at level 100, only printing).
Notation "'case' n " := (DestructHintSwitchIntCase n) (at level 100, only printing).
Notation "'default'" := (DestructHintSwitchIntDefault) (at level 100, only printing).

Section offsetof.
  Context `{!typeG Σ}.

  (*** OffsetOf *)
  Program Definition offsetof (s : struct_layout) (m : var_name) : type := {|
    ty_own β l := ∃ n, ⌜offset_of s.(sl_members) m = Some n⌝ ∗ l ◁ₗ{β} n @ int size_t
  |}%I.
  Next Obligation.
    iIntros (s m l E ?). iDestruct 1 as (n Hn) "H". iExists _. iSplitR => //. by iApply ty_share.
  Qed.

  Global Program Instance movable_offsetof s m : Movable (offsetof s m) := {|
    ty_layout := it_layout size_t;
    ty_own_val v := ∃ n, ⌜offset_of s.(sl_members) m = Some n⌝ ∗ v ◁ᵥ n @ int size_t
  |}%I.
  Next Obligation. iIntros (s m l). iDestruct 1 as (??)"Hn". iDestruct (ty_aligned with "Hn") as "$". Qed.
  Next Obligation. iIntros (s m l). iDestruct 1 as (??)"Hn". iDestruct (ty_size_eq with "Hn") as "$". Qed.
  Next Obligation.
    iIntros (s m l). iDestruct 1 as (??)"Hn".
    iDestruct (ty_deref with "Hn") as (v) "[Hl Hi]". iExists _. iFrame.
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (s m l v ?) "Hl". iDestruct 1 as (??)"Hn".
    iExists _. iSplit => //. iApply (@ty_ref with "[] Hl") => //. done.
  Qed.

  Global Program Instance offsetof_copyable s m : Copyable (offsetof s m).
  Next Obligation.
    iIntros (s m E l ?). iDestruct 1 as (n Hn) "Hl".
    iMod (copy_shr_acc with "Hl") as (???) "(Hl&H2&H3)" => //.
    iModIntro. iSplitR => //. iExists _, _. iFrame.
    iModIntro. iExists _. by iFrame.
  Qed.

  Lemma type_offset_of s m T:
    ⌜Some m ∈ s.(sl_members).*1⌝ ∗ (∀ v, T v (t2mt (offsetof s m))) -∗
    typed_val_expr (OffsetOf s m) T.
  Proof.
    iIntros "[%Hin HT] %Φ HΦ". move: Hin => /offset_of_from_in [n Hn].
    iApply wp_offset_of => //. iIntros "%v %Hv". iApply "HΦ" => //.
    iExists _. iSplit; first done. iPureIntro. apply val_to_of_Z in Hv.
    by eapply val_to_Z_to_int_repr_Z.
  Qed.

End offsetof.
Typeclasses Opaque offsetof.

(*** Tests *)
Section tests.
  Context `{!typeG Σ}.

  Example type_eq n1 n3 T:
    n1 ∈ size_t →
    n3 ∈ size_t →
    ⊢ typed_val_expr ((i2v n1 size_t +{IntOp size_t, IntOp size_t} i2v 0 size_t) = {IntOp size_t, IntOp size_t} i2v n3 size_t ) T.
  Proof.
    move => Hn1 Hn2.
    iApply type_bin_op.
    iApply type_bin_op.
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_arithop_int_int => //. iIntros (??). iSplit. {
      iPureIntro. unfold arith_op_sidecond, elem_of, int_elem_of_it, min_int, max_int in *; lia.
    }
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_relop_int_int => //.
  Abort.
End tests.
