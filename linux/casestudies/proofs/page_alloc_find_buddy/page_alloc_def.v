From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.page_alloc_find_buddy Require Import generated_code.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ}.
  Definition PAGE_SHIFT : Z := 12.
  Definition PAGE_SIZE : Z := 4096.
  Definition find_buddy (vmemmap : loc) (order : Z) (p : Z) : Z :=
    Z.lxor (p ≪ PAGE_SHIFT) (PAGE_SIZE ≪ order) ≫ PAGE_SHIFT.

  Lemma find_buddy_land_0 page order:
    0 ≤ order →
    Z.land (Z.lxor (page ≪ 12) (4096 ≪ order)) (Z.ones 12) = 0.
  Proof.
    move => ?. apply Z.bits_inj_iff' => n' ?.
    rewrite Z.bits_0 Z.land_spec Z.ones_spec// Z.lxor_spec !Z.shiftl_spec// andb_comm.
    case_bool_decide => //=.
    rewrite Z.testbit_neg_r /=; [|lia].
    {
      have : (n' - order) < 12 by lia.
      move: (n' - order) => n ?.
      destruct (decide (n < 0)); [ by rewrite Z.testbit_neg_r|].
      destruct (decide (n = 0)); subst; [done|].
      destruct (decide (n = 1)); subst; [done|].
      destruct (decide (n = 2)); subst; [done|].
      destruct (decide (n = 3)); subst; [done|].
      destruct (decide (n = 4)); subst; [done|].
      destruct (decide (n = 5)); subst; [done|].
      destruct (decide (n = 6)); subst; [done|].
      destruct (decide (n = 7)); subst; [done|].
      destruct (decide (n = 8)); subst; [done|].
      destruct (decide (n = 9)); subst; [done|].
      destruct (decide (n = 10)); subst; [done|].
      destruct (decide (n = 11)); subst; [done|].
      destruct (decide (n = 12)); subst; [done|].
      lia.
    }
  Qed.

  Lemma find_buddy_result_eq page range_start_idx order npages:
    0 ≤ order →
    (range_start_idx ≤ Z.lxor (page ≪ 12) (4096 ≪ order) ≫ 12
     ∧ Z.lxor (page ≪ 12) (4096 ≪ order) ≫ 12 < range_start_idx + npages)
      ↔
      (range_start_idx ≪ 12 ≤ Z.lxor (page ≪ 12) (4096 ≪ order)
       ∧ Z.lxor (page ≪ 12) (4096 ≪ order) < range_start_idx ≪ 12 + npages ≪ 12)
  .
  Proof.
    have ?:= find_buddy_land_0 page order.
    split; move => [H1 H2]; split.
    - move: H1 => /(Z_shiftl_le_mono_l 12).
      rewrite Z_shiftl_shiftr_0 //; lia.
    - move: H2 => /(Z_shiftl_lt_mono_l 12).
      rewrite Z_shiftl_distr_add // Z_shiftl_shiftr_0 //; lia.
    - move: H1 => /(Z_shiftr_le_mono_l 12).
      rewrite Z_shiftr_shiftl_0 //. lia.
    - move: H2 => /(Z_shiftr_lt_mono_l 12).
      rewrite -Z_shiftl_distr_add // Z_shiftr_shiftl_0 //.
      suff : Z.land ((range_start_idx + npages) ≪ 12) (Z.ones 12) = 0 by lia.
      apply Z.bits_inj_iff' => ??.
      rewrite Z.land_spec Z.ones_spec // !Z.shiftl_spec// Z.bits_0 andb_comm.
      case_bool_decide => //. rewrite Z.testbit_neg_r //. lia.
  Qed.
  Lemma find_buddy_result' page range_start_idx order npages n:
    0 ≤ order →
    0 ≤ range_start_idx →
    range_start_idx + npages ≤ n →
    (range_start_idx ≪ 12 ≤ Z.lxor (page ≪ 12) (4096 ≪ order)
     ∧ Z.lxor (page ≪ 12) (4096 ≪ order) < range_start_idx ≪ 12 + npages ≪ 12) →
    (0 ≤ Z.lxor (page ≪ 12) (4096 ≪ order) ≫ 12
     ∧ Z.lxor (page ≪ 12) (4096 ≪ order) ≫ 12 ≤ n).
  Proof. move => ??? /find_buddy_result_eq. lia.  Qed.
End type.
