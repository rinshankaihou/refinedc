From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

(** A [Strict] boolean can only have value 0 (false) or 1 (true). A [Relaxed]
boolean can have any value: 0 means false, anything else means true. *)
Inductive strictness := Strict | Relaxed.

Definition represents_boolean (stn: strictness) (n: Z) (b: bool) : Prop :=
  match stn with
  | Strict  => n = Z_of_bool b
  | Relaxed => bool_decide (n ≠ 0) = b
  end.

Lemma represents_boolean_eq (stn: strictness) (n: Z) (b: bool) :
  represents_boolean stn n b → bool_decide (n ≠ 0) = b.
Proof.
  destruct stn => //=. move => ->. by destruct b.
Qed.

Section generic_boolean.
  Context `{!typeG Σ}.

  Program Definition generic_boolean_inner_type (stn: strictness) (it: int_type) (b: bool) : type := {|
    ty_own β l :=
      ∃ v n, ⌜val_to_Z v it = Some n⌝ ∗
             ⌜represents_boolean stn n b⌝ ∗
             ⌜l `has_layout_loc` it⌝ ∗
             l ↦[β] v;
  |}%I.
  Next Obligation.
    iIntros (??????) "(%v&%n&%&%&%&Hl)". iExists v, n.
    do 3 (iSplitR; first done). by iApply heap_mapsto_own_state_share.
  Qed.

  Program Definition generic_boolean (stn: strictness) (it: int_type) : rtype := {|
    rty_type := bool;
    rty := generic_boolean_inner_type stn it;
  |}.

  Global Program Instance rmovable_generic_boolean stn it : RMovable (generic_boolean stn it) := {|
    rmovable b := {|
      ty_has_op_type ot mt := is_int_ot ot it;
      ty_own_val v := ∃ n, ⌜val_to_Z v it = Some n⌝ ∗ ⌜represents_boolean stn n b⌝;
    |}
  |}%I.
  Next Obligation. iIntros (?????? ->%is_int_ot_layout) "(%&%&_&_&$&_)". Qed.
  Next Obligation. iIntros (?????? ->%is_int_ot_layout [?[H _]]) "!%". by apply val_to_Z_length in H. Qed.
  Next Obligation. iIntros (???????) "(%v&%n&%&%&%&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (?????? v ->%is_int_ot_layout ?) "Hl (%n&%&%)". iExists v, n. eauto with iFrame. Qed.
  Next Obligation. iIntros (????????). apply: mem_cast_compat_int; [naive_solver|]. iPureIntro; naive_solver. Qed.

  Global Program Instance generic_boolean_copyable b stn it : Copyable (b @ generic_boolean stn it).
  Next Obligation.
    iIntros (??????? ->%is_int_ot_layout) "(%v&%n&%&%&%&Hl)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iSplitR; first done. iExists q, v. iFrame. iModIntro. eauto 6 with iFrame.
  Qed.

  Global Instance alloc_alive_generic_boolean b stn it β: AllocAlive (b @ generic_boolean stn it) β True.
  Proof.
    constructor. iIntros (l ?) "(%&%&%&%&%&Hl)".
    iApply (heap_mapsto_own_state_alloc with "Hl").
    erewrite val_to_Z_length; [|done]. have := bytes_per_int_gt_0 it. lia.
  Qed.

  Global Instance generic_boolean_timeless l b stn it:
    Timeless (l ◁ₗ b @ generic_boolean stn it)%I.
  Proof. apply _. Qed.

End generic_boolean.
Notation "generic_boolean< stn , it >" := (generic_boolean stn it)
  (only printing, format "'generic_boolean<' stn ',' it '>'") : printing_sugar.

Notation boolean := (generic_boolean Strict) (only parsing).
Notation "boolean< it >" := (boolean it)
  (only printing, format "'boolean<' it '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ}.

  Inductive destruct_hint_if_bool :=
  | DestructHintIfBool (b : bool).

  Lemma type_if_generic_boolean stn it (b : bool) v T1 T2 :
    destruct_hint (DHintDestruct _ b) (DestructHintIfBool b) (if b then T1 else T2) -∗
    typed_if (IntOp it) v (v ◁ᵥ b @ generic_boolean stn it) T1 T2.
  Proof.
    unfold destruct_hint. iIntros "Hs (%n&%Hv&%Hb)".
    rewrite <-(represents_boolean_eq stn n b); last done. eauto with iFrame.
  Qed.
  Global Instance type_if_generic_boolean_inst stn it b v :
    TypedIf (IntOp it) v (v ◁ᵥ b @ generic_boolean stn it)%I :=
    λ T1 T2, i2p (type_if_generic_boolean stn it b v T1 T2).

  Lemma type_assert_generic_boolean stn it (b : bool) s Q fn ls R v :
    (⌜b⌝ ∗ typed_stmt s fn ls R Q) -∗
    typed_assert (IntOp it) v (v ◁ᵥ b @ generic_boolean stn it) s fn ls R Q.
  Proof.
    iIntros "[%H $] (%n&%&%Hb)". destruct b; last by exfalso.
    iExists n. iSplit; first done. iPureIntro.
    by apply represents_boolean_eq, bool_decide_eq_true in Hb.
  Qed.
  Global Instance type_assert_generic_boolean_inst stn it b v :
    TypedAssert (IntOp it) v (v ◁ᵥ b @ generic_boolean stn it)%I :=
    λ s fn ls R Q, i2p (type_assert_generic_boolean _ _ _ _ _ _ _ _ _).
End programs.

Section boolean.
  Context `{!typeG Σ}.

  Lemma type_relop_boolean it v1 b1 v2 b2 T b op:
    match op with
    | EqOp rit => Some (eqb b1 b2       , rit)
    | NeOp rit => Some (negb (eqb b1 b2), rit)
    | _ => None
    end = Some (b, i32) →
    T (i2v (Z_of_bool b) i32) (t2mt (b @ boolean i32)) -∗
    typed_bin_op v1 (v1 ◁ᵥ b1 @ boolean it)
                 v2 (v2 ◁ᵥ b2 @ boolean it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT (%n1&%Hv1&%Hb1) (%n2&%Hv2&%Hb2) %Φ HΦ".
    have [v Hv]:= val_of_Z_bool_is_Some None i32 b.
    iApply (wp_binop_det_pure (i2v (Z_of_bool b) i32)).
    { rewrite /i2v Hv /=. destruct op, b1, b2; simplify_eq.
      all: split; [inversion 1; simplify_eq /=; done | move => ->]; simplify_eq /=.
      all: econstructor => //; by case_bool_decide. }
    iApply "HΦ"; last done. iExists (Z_of_bool b).
    iSplit; [by destruct b | done].
  Qed.

  Global Program Instance type_eq_boolean_inst it v1 b1 v2 b2:
    TypedBinOpVal v1 (b1 @ (boolean it))%I
                  v2 (b2 @ (boolean it))%I
                  (EqOp i32) (IntOp it) (IntOp it) :=
    λ T, i2p (type_relop_boolean it v1 b1 v2 b2 T (eqb b1 b2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_ne_boolean_inst it v1 b1 v2 b2:
    TypedBinOpVal v1 (b1 @ (boolean it))%I
                  v2 (b2 @ (boolean it))%I
                  (NeOp i32) (IntOp it) (IntOp it) :=
    λ T, i2p (type_relop_boolean it v1 b1 v2 b2 T (negb (eqb b1 b2)) _ _).
  Next Obligation. done. Qed.

  (* TODO: replace this with a typed_cas once it is refactored to take E as an argument. *)
  Lemma wp_cas_suc_boolean it b1 b2 bd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    b1 = b2 →
    l1 ◁ₗ b1 @ boolean it -∗
    l2 ◁ₗ b2 @ boolean it -∗
    vd ◁ᵥ bd @ boolean it -∗
    ▷ (l1 ◁ₗ bd @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ Φ (val_of_bool true)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? ->) "(%v1&%n1&%&%&%&Hl1) (%v2&%n2&%&%&%&Hl2) (%n&%&%) HΦ/=".
    iApply (wp_cas_suc with "Hl1 Hl2") => //.
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by eapply val_to_Z_length. }
    { simpl in *. by simplify_eq. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _, _; by iFrame.
  Qed.

  Lemma wp_cas_fail_boolean it b1 b2 bd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    b1 ≠ b2 →
    l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ vd ◁ᵥ bd @ boolean it -∗
    ▷ (l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b1 @ boolean it -∗ Φ (val_of_bool false)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (??) "(%v1&%n1&%&%&%&Hl1) (%v2&%n2&%&%&%&Hl2) (%n&%&%) HΦ/=".
    iApply (wp_cas_fail with "Hl1 Hl2") => //.
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by eapply val_to_Z_length. }
    { simpl in *. simplify_eq. by destruct b1, b2. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _, _; by iFrame.
  Qed.

  Lemma type_val_boolean b T:
    (T (t2mt (b @ boolean bool_it))) -∗ typed_value (val_of_bool b) T.
  Proof.
    iIntros "HT". iExists _. iFrame.
    iExists (Z_of_bool b). destruct b; eauto.
  Qed.
  Global Instance type_val_boolean_inst b : TypedValue (val_of_bool b) :=
    λ T, i2p (type_val_boolean b T).

  Lemma type_cast_boolean b it1 it2 v T:
    (∀ v, T v (t2mt (b @ boolean it2))) -∗
    typed_un_op v (v ◁ᵥ b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT (%n&%Hv&%Hb) %Φ HΦ". move: Hb => /= ?. subst n.
    have [??] := val_of_Z_bool_is_Some (val_to_byte_prov v) it2 b.
    iApply wp_cast_int => //. iApply ("HΦ" with "[] HT") => //.
    iExists _. iSplit; last done. iPureIntro. by eapply val_to_of_Z.
  Qed.
  Global Instance type_cast_bool_inst b it1 it2 v:
    TypedUnOpVal v (b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) :=
    λ T, i2p (type_cast_boolean b it1 it2 v T).

End boolean.
Typeclasses Opaque generic_boolean_inner_type.

Notation "'if' p " := (DestructHintIfBool p) (at level 100, only printing).
