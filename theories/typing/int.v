From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section int.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition int_inner_type (it : int_type) (n : Z) : type := {|
    ty_own β l := (∃ v, ⌜val_of_int n it = Some v⌝ ∗ ⌜l `has_layout_loc` it⌝ ∗ l ↦[β] v)%I
  |}.
  Next Obligation.
    iIntros (it n l). iDestruct 1 as (v Hv Hl) "H". iExists _. do 2 iSplitR => //. by iApply heap_mapsto_own_state_share.
  Qed.

  Program Definition int (it : int_type) : rtype := {|
    rty_type := Z;
    rty := int_inner_type it
  |}.

  Global Program Instance rmovable_int it : RMovable (int it) := {|
    rmovable n := {|
      ty_layout := it_layout it;
      ty_own_val v := ⌜val_of_int n it = Some v⌝%I;
  |} |}.
  Next Obligation. iIntros (it n l). by iDestruct 1 as (???)"?". Qed.
  Next Obligation. by iIntros (it n v ?%val_of_int_length). Qed.
  Next Obligation.
    iIntros (it n l). iDestruct 1 as (v Hl Hv) "Hl".
    iExists _. by iFrame.
  Qed.
  Next Obligation. iIntros (it n l v Hly) "Hl". iIntros (?). iExists _. by iFrame. Qed.
  Next Obligation. iIntros (it x1 x2). done. Qed.

  Lemma int_loc_in_bounds l β n it:
     l ◁ₗ{β} n @ int it -∗ loc_in_bounds l (bytes_per_int it).
  Proof.
    iIntros "Hl". iDestruct "Hl" as (? <-%val_of_int_length) "[% Hl]".
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
    iIntros "Hl".
    destruct β.
    - iDestruct (ty_deref with "Hl") as (?) "[_ %]".
      iPureIntro. by eapply val_of_int_in_range.
    - rewrite /ty_own /=. iDestruct "Hl" as (?) "[% _]".
      iPureIntro. by eapply val_of_int_in_range.
  Qed.

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance int_copyable x it : Copyable (x @ int it).
  Next Obligation.
    iIntros (x it E l ?). iDestruct 1 as (v Hv Hl) "Hl".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //.
    by iIntros "_".
  Qed.

End int.
(* Typeclasses Opaque int. *)
Notation "int< it >" := (int it) (only printing, format "'int<' it '>'") : printing_sugar.

(* TODO: move this to an extra file? *)
Section boolean.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition boolean_inner_type (it : int_type) (b : bool) : type := int_inner_type it (Z_of_bool b).

  Program Definition boolean (it : int_type) : rtype := {|
    rty_type := bool;
    rty := boolean_inner_type it
  |}.

  Global Program Instance rmovable_boolean it : RMovable (boolean it) := {|
    rmovable b := {|
      ty_layout := it_layout it;
      ty_own_val v := ⌜val_of_int (Z_of_bool b) it = Some v⌝%I;
  |} |}.
  Next Obligation. iIntros (it n l). by iDestruct 1 as (???)"?". Qed.
  Next Obligation. by iIntros (it n v ?%val_of_int_length). Qed.
  Next Obligation.
    iIntros (it n l). iDestruct 1 as (v Hv Hl) "Hl".
    iExists _. by iFrame.
  Qed.
  Next Obligation. iIntros (it n l v ?) "Hl". iIntros (?). iExists _. by iFrame. Qed.
  Next Obligation. iIntros (it x1 x2). done. Qed.

End boolean.
Notation "boolean< it >" := (boolean it) (only printing, format "'boolean<' it '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ}.

  (*** int *)
  Lemma type_val_int n it T:
    (⌜n ∈ it⌝ ∗ T (t2mt (n @ (int it)))) -∗ typed_value (i2v n it) T.
  Proof. iDestruct 1 as ([v Hv]%val_of_int_is_some) "HT". iExists  _. iFrame. by rewrite /i2v Hv. Qed.
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
    move => Hop. iIntros "HT" (Hv1 Hv2 Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_of_int_in_range.
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2.
    iApply (wp_binop_det (i2v (Z_of_bool b) i32)). iSplit.
    { iIntros (σ v') "_ !%". split; last (move => ->; by econstructor).
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

  Lemma type_arithop_int_int it v1 n1 v2 n2 T n op:
   match op with
    | AddOp => Some (n1 + n2)
    | SubOp => Some (n1 - n2)
    | MulOp => Some (n1 * n2)
    | AndOp => Some (Z.land n1 n2)
    | OrOp => Some (Z.lor n1 n2)
    | XorOp => Some (Z.lxor n1 n2)
    | ShlOp => Some (n1 ≪ n2)
    | ShrOp => Some (n1 ≫ n2)
    | _ => None
    end = Some n →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜n ∈ it⌝ ∗ T (i2v n it) (t2mt (n @ int it))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros (Hop) "HT". iIntros (Hv1 Hv2 Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as ([v Hv]%val_of_int_is_some) "HT".
    1-2: iPureIntro; by apply: val_of_int_in_range.
    move: (Hv) => /val_of_int_in_range ?.
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2. rewrite /i2v Hv/=.
    iApply (wp_binop_det v). iSplit.
    - iIntros (σ v') "_ !%". split.
      + destruct op => //.
        all: inversion 1; simplify_eq/=.
        all: destruct it as [? []]; simplify_eq/= => //.
        all: by rewrite ->it_in_range_mod in * => //; simplify_eq.
      + move => ->; destruct op => //; econstructor => //.
        all: destruct it as [? []]; simplify_eq/= => //.
        all: by rewrite it_in_range_mod; simplify_eq/=.
    - iIntros "!>". iApply "HΦ"; last done.  by iPureIntro.
  Qed.
  Lemma type_arithop_int_int_div_mod it v1 n1 v2 n2 T n op:
    match op with
    | DivOp => Some (n1 `quot` n2)
    | ModOp => Some (n1 `rem` n2)
    | _ => None
    end = Some n →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜n2 ≠ 0⌝ ∗ ⌜n ∈ it⌝ ∗ T (i2v n it) (t2mt (n @ int it))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros (Hop) "HT". iIntros (Hv1 Hv2 Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as (Hn [v Hv]%val_of_int_is_some) "HT".
    1-2: iPureIntro; by apply: val_of_int_in_range.
    move: (Hv) => /val_of_int_in_range ?.
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2. rewrite /i2v Hv/=.
    iApply (wp_binop_det v). iSplit.
    - iIntros (σ v') "_ !%". split.
      + destruct op => //.
        all: inversion 1; destruct n2; simplify_eq/=.
        all: destruct it as [? []]; simplify_eq/= => //.
        all: by rewrite ->it_in_range_mod in * => //; simplify_eq.
      + move => ->; destruct op, n2 => //; econstructor => // => //.
        all: destruct it as [? []]; simplify_eq/= => //.
        all: by rewrite it_in_range_mod; simplify_eq/=.
    - iIntros "!>". iApply "HΦ"; last done.  by iPureIntro.
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
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I DivOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_div_mod it v1 n1 v2 n2 T (n1 `quot` n2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_mod_int_int_inst it v1 n1 v2 n2:
    TypedBinOpVal v1 (n1 @ int it)%I v2 (n2 @ int it)%I ModOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_div_mod it v1 n1 v2 n2 T (n1 `rem` n2) _ _).
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
    unfold destruct_hint. iIntros "Hs" (Hb%val_to_of_int) => /=.
    iExists _, _. do 2 iSplit => //. by do ! case_decide.
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
    unfold destruct_hint. iIntros "HT" (Hv%val_to_of_int). iExists n. iSplit => //.
    iInduction m as [] "IH" using map_ind; simplify_map_eq => //.
    { iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro. rewrite map_to_list_empty. set_solver. }
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
    iIntros "HT". iIntros (Hv Φ) "HΦ".
    move: Hv (Hv) => /val_to_of_int ? /val_of_int_in_range[Hl Hu].
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    have ? : val_of_int (- n) it = Some (i2v (- n) it). {
      have [|? Hv'] := val_of_int_is_some it (- n); last by rewrite /i2v Hv'.
      unfold elem_of, int_elem_of_it, max_int, min_int in *.
      destruct it as [?[]] => //; simpl in *; lia.
    }
    iApply wp_neg_int => //. by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_neg_int_inst n it v:
    TypedUnOpVal v (n @ int it)%I NegOp (IntOp it) :=
    λ T, i2p (type_neg_int n it v T).

  Lemma type_cast_int n it1 it2 v T:
    (⌜n ∈ it1⌝ -∗ ⌜n ∈ it2⌝ ∗ T (i2v n it2) (t2mt (n @ int it2))) -∗
    typed_un_op v (v ◁ᵥ n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT". iIntros (Hv Φ) "HΦ".
    iDestruct ("HT" with "[]" ) as ([v' Hv']%val_of_int_is_some) "HT".
    1: iPureIntro; by apply: val_of_int_in_range.
    move: Hv => /val_to_of_int Hv. rewrite /i2v Hv'/=.
    iApply wp_cast_int => //. iApply ("HΦ" with "[] HT") => //.
  Qed.
  Global Instance type_cast_int_inst n it1 it2 v:
    TypedUnOpVal v (n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) :=
    λ T, i2p (type_cast_int n it1 it2 v T).

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
    iIntros (Hop) "HT". iIntros (Hv1 Hv2 Φ) "HΦ".
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2.
    iApply (wp_binop_det (i2v (Z_of_bool b) i32)). iSplit.
    { iIntros (σ v) "_ !%". destruct op, b1, b2; simplify_eq;
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
    unfold destruct_hint. iIntros "Hs" (Hb%val_to_of_int) => /=.
    iExists _, _. do 2 iSplit => //.
    by destruct b.
  Qed.
  Global Instance type_if_bool_inst it b v : TypedIf (IntOp it) v (b @ boolean it) :=
    λ T1 T2, i2p (type_if_bool it b v T1 T2).

  Lemma type_assert_bool {B} (b : bool) s Q fn ls (fr : B → _) v :
    (⌜b⌝ ∗ typed_stmt s fn ls fr Q) -∗
    typed_assert v (b @ boolean bool_it) s fn ls fr Q.
  Proof.
    iIntros "[% Hs]" (Hb%val_to_of_int) => /=. iExists _. iSplit => //. iFrame. by destruct b.
  Qed.
  Global Instance type_assert_bool_inst b v : TypedAssert v (b @ boolean bool_it) :=
    λ B s fn ls fr Q, i2p (type_assert_bool _ _ _ _ _ _ _).

  Lemma type_cast_bool b it1 it2 v T:
    (T (i2v (Z_of_bool b) it2) (t2mt (b @ boolean it2))) -∗
    typed_un_op v (v ◁ᵥ b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT". iIntros (Hv Φ) "HΦ".
    move: Hv => /val_to_of_int Hv.
    iApply wp_cast_int => //=. by apply val_of_int_bool.
    iApply ("HΦ" with "[] HT") => //. iPureIntro => /=. by apply val_of_int_bool.
  Qed.
  Global Instance type_cast_bool_inst b it1 it2 v:
    TypedUnOpVal v (b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) :=
    λ T, i2p (type_cast_bool b it1 it2 v T).

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
    iDestruct 1 as ([n Hn]%offset_of_from_in) "HT".
    iIntros (Φ) "HΦ". iApply wp_offset_of => //.
    iIntros (v Hv). iApply "HΦ" => //. iExists _. by iSplit.
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
      iPureIntro. unfold elem_of, int_elem_of_it, min_int, max_int in *; lia.
    }
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_relop_int_int => //.
  Abort.
End tests.
