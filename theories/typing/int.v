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

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance int_copyable x it : Copyable (x @ int it).
  Next Obligation.
    iIntros (x it E l ?). iDestruct 1 as (v Hv Hl) "Hl".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //.
    by iIntros "_".
  Qed.

  Lemma int_val_to_int_Some n v it:
    v ◁ᵥ n @ int it -∗ ⌜val_to_int v it = Some n⌝.
  Proof. iIntros "%". iPureIntro. by apply val_to_of_int. Qed.

End int.
(* Typeclasses Opaque int. *)

(* TODO: move this to an extra file? *)
Section bool.
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

End bool.

Section programs.
  Context `{!typeG Σ}.

  (*** int *)
  Lemma type_val_int n it T:
    (⌜it_in_range it n⌝ ∗ T (t2mt (n @ (int it)))) -∗ typed_value (i2v n it) T.
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
    (⌜it_in_range it n1⌝ -∗ ⌜it_in_range it n2⌝ -∗ T (i2v (Z_of_bool b) i32) (t2mt (b @ boolean i32))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros (Hop) "HT". iIntros (Hv1 Hv2 Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_of_int_in_range.
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2.
    iApply (wp_binop); first eauto using RelOpII.
    iIntros "!#" (v' h Heq). inversion Heq; destruct op; simplify_eq; iApply "HΦ" => //; by iPureIntro; repeat case_bool_decide.
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
    (⌜it_in_range it n1⌝ -∗ ⌜it_in_range it n2⌝ -∗ ⌜it_in_range it n⌝ ∗ T (i2v n it) (t2mt (n @ int it))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros (Hop) "HT". iIntros (Hv1 Hv2 Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as ([v Hv]%val_of_int_is_some) "HT".
    1-2: iPureIntro; by apply: val_of_int_in_range.
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2. rewrite /i2v Hv/=.
    iApply (wp_binop); first by destruct op; eauto using ArithOpII.
    iIntros "!#" (v' h Heq). inversion Heq; destruct op; simplify_eq; iApply "HΦ" => //; by iPureIntro.
  Qed.
  Lemma type_arithop_int_int_div_mod it v1 n1 v2 n2 T n op:
    match op with
    | DivOp => Some (n1 `quot` n2)
    | ModOp => Some (n1 `rem` n2)
    | _ => None
    end = Some n →
    (⌜it_in_range it n1⌝ -∗ ⌜it_in_range it n2⌝ -∗ ⌜n2 ≠ 0⌝ ∗ ⌜it_in_range it n⌝ ∗ T (i2v n it) (t2mt (n @ int it))) -∗
      typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros (Hop) "HT". iIntros (Hv1 Hv2 Φ) "HΦ".
    iDestruct ("HT" with "[] []" ) as (Hn [v Hv]%val_of_int_is_some) "HT".
    1-2: iPureIntro; by apply: val_of_int_in_range.
    move: Hv1 Hv2 => /val_to_of_int Hv1 /val_to_of_int Hv2. rewrite /i2v Hv/=.
    iApply wp_binop; first by intros; destruct op; apply: ArithOpII => //; by case_match.
    iIntros "!#" (v' h Heq). inversion Heq; destruct op, n2; simplify_eq; iApply "HΦ" => //; by iPureIntro.
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

  Lemma type_if_int {B} n s1 s2 Q fn ls (fr : B → _) v :
    destruct_hint (DHintDecide (n ≠ 0)) (DestructHintIfInt n)
    (if decide (n ≠ 0) then typed_stmt s1 fn ls fr Q else typed_stmt s2 fn ls fr Q) -∗
    typed_if v (n @ int bool_it) s1 s2 fn ls fr Q.
  Proof. unfold destruct_hint. iIntros "Hs" (Hb%val_to_of_int) => /=. iExists _. iSplit => //. by do ! case_decide. Qed.
  Global Instance type_if_int_inst n v : TypedIf v (n @ int bool_it) :=
    λ B s1 s2 fn ls fr Q, i2p (type_if_int n s1 s2 Q fn ls fr v).

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
    (⌜it_in_range it n⌝ -∗ ⌜it.(it_signed)⌝ ∗ ⌜n ≠ it_min it⌝ ∗ T (i2v (-n) it) (t2mt ((-n) @ int it))) -∗
    typed_un_op v (v ◁ᵥ n @ int it)%I (NegOp) (IntOp it) T.
  Proof.
    iIntros "HT". iIntros (Hv Φ) "HΦ".
    move: Hv (Hv) => /val_to_of_int ? /val_of_int_in_range[Hl Hu].
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    have ? : val_of_int (- n) it = Some (i2v (- n) it). {
      have [|? Hv'] := val_of_int_is_some it (- n); last by rewrite /i2v Hv'.
      unfold it_in_range, it_max, it_min in *.
      destruct it as [?[]] => //; simpl in *; lia.
    }
    iApply wp_neg_int => //. by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_neg_int_inst n it v:
    TypedUnOpVal v (n @ int it)%I NegOp (IntOp it) :=
    λ T, i2p (type_neg_int n it v T).

  Lemma type_cast_int n it1 it2 v T:
    (⌜it_in_range it1 n⌝ -∗ ⌜it_in_range it2 n⌝ ∗ T (i2v n it2) (t2mt (n @ int it2))) -∗
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
  Lemma type_val_bool b T:
    (T (t2mt (b @ boolean bool_it))) -∗ typed_value (val_of_bool b) T.
  Proof. iIntros "HT". iExists _. iFrame. by destruct b. Qed.
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
    iApply (wp_binop (i2v (Z_of_bool b) i32)).
    { intros. by destruct op => //; apply: RelOpII => //; destruct b1, b2. }
    iIntros "!#" (v' h Heq).
    inversion Heq; destruct op; simplify_eq; destruct b1, b2; iApply "HΦ" => //=; by iPureIntro.
  Qed.

  Global Program Instance type_eq_bool_bool_inst it v1 b1 v2 b2:
    TypedBinOpVal v1 (b1 @ (boolean it))%I v2 (b2 @ (boolean it))%I EqOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_bool_bool it v1 b1 v2 b2 T (eqb b1 b2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_ne_bool_bool_inst it v1 b1 v2 b2:
    TypedBinOpVal v1 (b1 @ (boolean it))%I v2 (b2 @ (boolean it))%I NeOp (IntOp it) (IntOp it) := λ T, i2p (type_relop_bool_bool it v1 b1 v2 b2 T (negb (eqb b1 b2)) _ _).
  Next Obligation. done. Qed.

  Lemma type_if_bool {B} (b : bool) s1 s2 Q fn ls (fr : B → _) v :
    destruct_hint (DHintDestruct _ b) (DestructHintIfBool b)
    (if b then typed_stmt s1 fn ls fr Q else typed_stmt s2 fn ls fr Q) -∗
    typed_if v (b @ boolean bool_it) s1 s2 fn ls fr Q.
  Proof. unfold destruct_hint. iIntros "Hs" (Hb%val_to_of_int) => /=. iExists _. iSplit => //. by destruct b. Qed.
  Global Instance type_if_bool_inst b v : TypedIf v (b @ boolean bool_it) :=
    λ B s1 s2 fn ls fr Q, i2p (type_if_bool _ _ _ _ _ _ _ _).

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
    TypedBinOp v1 (v1 ◁ᵥ b1 @ boolean it1)%I v2 (v2 ◁ᵥ n2 @ int it2)%I op (IntOp it3) (IntOp it4) :=
    λ T, i2p (type_binop_bool_int it1 it2 it3 it4 v1 b1 v2 n2 T op).

  Lemma type_binop_int_bool it1 it2 it3 it4 v1 b1 v2 n2 T op:
    typed_bin_op v1 (v1 ◁ᵥ n2 @ int it2) v2 (v2 ◁ᵥ (Z_of_bool b1) @ int it1) op (IntOp it3) (IntOp it4) T -∗
    typed_bin_op v1 (v1 ◁ᵥ n2 @ int it2) v2 (v2 ◁ᵥ b1 @ boolean it1) op (IntOp it3) (IntOp it4) T.
  Proof. iIntros "HT". iApply "HT". Qed.
  Global Instance type_binop_int_bool_inst it1 it2 it3 it4 v1 b1 v2 n2 op:
    TypedBinOp v1 (v1 ◁ᵥ n2 @ int it2)%I v2 (v2 ◁ᵥ b1 @ boolean it1)%I op (IntOp it3) (IntOp it4) :=
    λ T, i2p (type_binop_int_bool it1 it2 it3 it4 v1 b1 v2 n2 T op).

End programs.
Typeclasses Opaque int_inner_type boolean_inner_type.

(*** Tests *)
Section tests.
  Context `{!typeG Σ}.

  Example type_eq n1 n3 T:
    it_in_range size_t n1 →
    it_in_range size_t n3 →
    ⊢ typed_val_expr ((i2v n1 size_t +{IntOp size_t, IntOp size_t} i2v 0 size_t) = {IntOp size_t, IntOp size_t} i2v n3 size_t ) T.
  Proof.
    move => Hn1 Hn2.
    iApply type_bin_op.
    iApply type_bin_op.
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_arithop_int_int => //. iIntros (??). iSplit. {
      iPureIntro. unfold it_in_range, it_min, it_max in *; lia.
    }
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_relop_int_int => //.
  Abort.
End tests.
