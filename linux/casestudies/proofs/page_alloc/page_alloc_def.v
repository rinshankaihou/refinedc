From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.page_alloc Require Import generated_code.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ}.
  Definition PAGE_SIZE : Z := 4096.
  Definition PAGE_LAYOUT (n : Z) := ly_with_align (Z.to_nat (PAGE_SIZE * n)) (Z.to_nat (PAGE_SIZE * n)).
  Definition hyp_phys_to_page (vmemmap : loc) (p : Z) : Z. Admitted.
  Definition hyp_page_to_phys (vmemmap : loc) (page : Z) : Z. Admitted.
  Definition hyp_page_to_virt (vmemmap : loc) (page : loc) : loc. Admitted.

  Definition list_node (next : option (option type)) : type. Admitted.
  Definition idx_to_node (vmemmap : loc) (vmemmap_len :nat) (next : option (option Z) ) : option (option type) :=
    (λ no : option _, (λ n, array_ptr struct_hyp_page vmemmap n vmemmap_len) <$> no) <$> next.

  Lemma subsume_list_node n1 n2 l β T:
    ⌜n1 = n2⌝ ∗ T
    ⊢ subsume (l ◁ₗ{β} list_node n1) (l ◁ₗ{β} list_node n2) T.
  Proof. by iIntros "[-> $] $". Qed.
  Global Instance subsume_list_node_inst n1 n2 l β:
    SubsumePlace l β (list_node n1) (list_node n2) :=
    λ T, i2p (subsume_list_node n1 n2 l β T).

  Global Instance inj_hyp_page_map {A B C D E F} pool vmemmap npages : Inj (=) (=) (λ '(ref_count, order, next), (pool, vmemmap, npages, ref_count, order, next) : (A * B * C * D * E * F)).
  Proof. move => [[??]?] [[??]?]. naive_solver. Qed.

  Global Instance assume_inj_list_node vmemmap len : AssumeInj (=) (=) (λ h, list_node (idx_to_node vmemmap len h)).
  Proof. done. Qed.

  Definition find_buddy (vmemmap : loc) (order : Z) (p : Z) : Z. Admitted.

  Lemma find_buddy_neq vmemmap order page :
    find_buddy vmemmap order page ≠ page.
  Proof. Admitted.

  Lemma simplify_goal_place_find_buddy_lt vmemmap p order β ty T `{!CanSolve (p < find_buddy vmemmap order p)}:
    T (hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ find_buddy vmemmap order p) ◁ₗ{β} ty)
    ⊢ simplify_goal ((hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ p) +ₗ ly_size (PAGE_LAYOUT (1 ≪ order))) ◁ₗ{β} ty) T.
  Proof. Admitted.
  Global Instance simplify_goal_place_find_buddy_lt_inst vmemmap p order β ty `{!CanSolve (p < find_buddy vmemmap order p)}:
    SimplifyGoalPlace ((hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ p) +ₗ ly_size (PAGE_LAYOUT (1 ≪ order)))) β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_find_buddy_lt vmemmap p order β ty T).
  Lemma simplify_goal_place_find_buddy_gt vmemmap p order β ty T:
    T (⌜find_buddy vmemmap order p < p⌝ ∗ hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ p) ◁ₗ{β} ty)
    ⊢ simplify_goal ((hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ find_buddy vmemmap order p) +ₗ ly_size (PAGE_LAYOUT (1 ≪ order))) ◁ₗ{β} ty) T.
  Proof. Admitted.
  Global Instance simplify_goal_place_find_buddy_gt_inst vmemmap p order β ty:
    SimplifyGoalPlace ((hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ find_buddy vmemmap order p) +ₗ ly_size (PAGE_LAYOUT (1 ≪ order)))) β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_find_buddy_gt vmemmap p order β ty T).

  Global Instance simpl_page_layout_size_le n1 n2:
    SimplAndUnsafe true (ly_size (PAGE_LAYOUT n1) ≤ ly_size (PAGE_LAYOUT n2))%nat (λ T, n1 ≤ n2 ∧ T).
  Proof. rewrite /PAGE_LAYOUT/ly_size/= => ? [??]. split => //. rewrite /PAGE_SIZE. lia. Qed.
  Global Instance simpl_shiftl_monol_le n m1 m2 `{!CanSolve (0 < n ∧ 0 ≤ m1 ∧ 0 ≤ m2)}:
    SimplBoth (n ≪ m1 ≤ n ≪ m2) (m1 ≤ m2).
  Proof.
    unfold CanSolve in *.
      by rewrite /SimplBoth !Z.shiftl_mul_pow2 -?Z.mul_le_mono_pos_l -?Z.pow_le_mono_r_iff; [|lia..].
  Qed.
  Global Instance simpl_page_layout_shift order `{!CanSolve (0 ≤ order)}:
    SimplAndRel (=) (ly_size (PAGE_LAYOUT (1 ≪ (order + 1))) - ly_size (PAGE_LAYOUT (1 ≪ order)))%nat
                (ly_size (PAGE_LAYOUT (1 ≪ order))) (λ T, T).
  Proof.
    unfold CanSolve in *. split; [|naive_solver] => ?. split => //.
    have ?:= Z.pow_nonneg 2 order.
    rewrite/ly_size/=/PAGE_SIZE !Z.shiftl_mul_pow2  -?Z2Nat.inj_sub -?Z.mul_sub_distr_l ?Z.pow_add_r /=; nia.
  Qed.
End type.

Global Typeclasses Opaque PAGE_LAYOUT.
Global Opaque PAGE_LAYOUT.

Ltac enrich_context_tac ::=
  enrich_context_base;
  repeat match goal with
         | |- context C [ find_buddy ?vmemmap ?order ?page ] =>
           let G := context C[enrich_marker find_buddy vmemmap order page] in
           change_no_check G;
           try have ?:=find_buddy_neq vmemmap order page
         end.
