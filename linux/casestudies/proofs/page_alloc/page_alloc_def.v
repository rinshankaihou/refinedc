From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.page_alloc Require Import generated_code.
Set Default Proof Using "Type".

Remove Hints find_in_context_type_val_P_own_singleton_inst : typeclass_instances.

Section type.
  Context `{!typeG Σ}.

  Definition list_node (next : option (option type)) : type. Admitted.
  Definition idx_to_node (vmemmap : loc) (vmemmap_len :nat) (next : option (option Z) ) : option (option type) := (λ no, (λ n, array_ptr struct_hyp_page vmemmap n vmemmap_len) <$> no) <$> next.

  Lemma subsume_list_node n1 n2 l β T:
    ⌜n1 = n2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} list_node n1) (l ◁ₗ{β} list_node n2) T.
  Proof. by iIntros "[-> $] $". Qed.
  Global Instance subsume_list_node_inst n1 n2 l β:
    SubsumePlace l β (list_node n1) (list_node n2) :=
    λ T, i2p (subsume_list_node n1 n2 l β T).

  Global Instance inj_hyp_page_map {A B C D E F} : Inj (=) (=) (λ '(ref_count, order, next), (pool, vmemmap, npages, ref_count, order, next) : (A * B * C * D * E * F)).
  Proof. move => ??? [[??]?] [[??]?]. naive_solver. Qed.

  Global Instance assume_inj_list_node vmemmap len : AssumeInj (=) (=) (λ h, list_node (idx_to_node vmemmap len h)).
  Proof. done. Qed.

  Definition find_buddy (vmemmap : loc) (order : Z) (p : Z) : Z. Admitted.

  Lemma find_buddy_neq vmemmap order page :
    find_buddy vmemmap order page ≠ page.
  Proof. Admitted.

End type.

Ltac enrich_context_tac ::=
  enrich_context_base;
  repeat match goal with
         | |- context C [ find_buddy ?vmemmap ?order ?page ] =>
           let G := context C[enrich_marker find_buddy vmemmap order page] in
           change_no_check G;
           try have ?:=find_buddy_neq vmemmap order page
         end.
