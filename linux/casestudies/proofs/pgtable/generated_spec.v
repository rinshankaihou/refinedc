From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [kvm_pgtable_mm_ops]. *)
  Definition kvm_pgtable_mm_ops_rec : (mm_callbacks → type) → (mm_callbacks → type) := (λ self mm_ops,
    struct struct_kvm_pgtable_mm_ops [@{type}
      (function_ptr (fn(∀ (p, a) : loc * Z; p @ &own (a @ int u64); True) → ∃ () : (), (mm_ops.(virt_to_phys) a) @ bitfield_raw u64; True))
    ]
  )%I.
  Global Typeclasses Opaque kvm_pgtable_mm_ops_rec.

  Global Instance kvm_pgtable_mm_ops_rec_le : TypeMono kvm_pgtable_mm_ops_rec.
  Proof. solve_type_proper. Qed.

  Definition kvm_pgtable_mm_ops : rtype (mm_callbacks) := {|
    rty r__ := kvm_pgtable_mm_ops_rec (type_fixpoint kvm_pgtable_mm_ops_rec) r__
  |}.

  Lemma kvm_pgtable_mm_ops_unfold (mm_ops : mm_callbacks):
    (mm_ops @ kvm_pgtable_mm_ops)%I ≡@{type} (
      struct struct_kvm_pgtable_mm_ops [@{type}
        (function_ptr (fn(∀ (p, a) : loc * Z; p @ &own (a @ int u64); True) → ∃ () : (), (mm_ops.(virt_to_phys) a) @ bitfield_raw u64; True))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 kvm_pgtable_mm_ops_rec). Qed.

  Definition kvm_pgtable_mm_ops_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (kvm_pgtable_mm_ops_unfold patt__) with 100%N].
  Global Existing Instance kvm_pgtable_mm_ops_simplify_hyp_place_inst_generated.
  Definition kvm_pgtable_mm_ops_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (kvm_pgtable_mm_ops_unfold patt__) with 100%N].
  Global Existing Instance kvm_pgtable_mm_ops_simplify_goal_place_inst_generated.

  Definition kvm_pgtable_mm_ops_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (kvm_pgtable_mm_ops_unfold patt__) with 100%N].
  Global Existing Instance kvm_pgtable_mm_ops_simplify_hyp_val_inst_generated.
  Definition kvm_pgtable_mm_ops_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (kvm_pgtable_mm_ops_unfold patt__) with 100%N].
  Global Existing Instance kvm_pgtable_mm_ops_simplify_goal_val_inst_generated.

  (* Definition of type [hyp_map_data]. *)
  Definition hyp_map_data_rec : (Z * Attr * mm_callbacks * loc → type) → (Z * Attr * mm_callbacks * loc → type) := (λ self patt__,
    let phys := patt__.1.1.1 in
    let attr := patt__.1.1.2 in
    let mm_ops := patt__.1.2 in
    let o := patt__.2 in
    struct struct_hyp_map_data [@{type}
      (phys @ (int (u64))) ;
      (attr @ (bitfield (Attr))) ;
      (o @ (&own (mm_ops @ (kvm_pgtable_mm_ops))))
    ]
  )%I.
  Global Typeclasses Opaque hyp_map_data_rec.

  Global Instance hyp_map_data_rec_le : TypeMono hyp_map_data_rec.
  Proof. solve_type_proper. Qed.

  Definition hyp_map_data : rtype (Z * Attr * mm_callbacks * loc) := {|
    rty r__ := hyp_map_data_rec (type_fixpoint hyp_map_data_rec) r__
  |}.

  Lemma hyp_map_data_unfold (patt__ : Z * Attr * mm_callbacks * loc):
    (patt__ @ hyp_map_data)%I ≡@{type} (
      let phys := patt__.1.1.1 in
      let attr := patt__.1.1.2 in
      let mm_ops := patt__.1.2 in
      let o := patt__.2 in
      struct struct_hyp_map_data [@{type}
        (phys @ (int (u64))) ;
        (attr @ (bitfield (Attr))) ;
        (o @ (&own (mm_ops @ (kvm_pgtable_mm_ops))))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 hyp_map_data_rec). Qed.

  Definition hyp_map_data_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (hyp_map_data_unfold patt__) with 100%N].
  Global Existing Instance hyp_map_data_simplify_hyp_place_inst_generated.
  Definition hyp_map_data_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (hyp_map_data_unfold patt__) with 100%N].
  Global Existing Instance hyp_map_data_simplify_goal_place_inst_generated.

  Definition hyp_map_data_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (hyp_map_data_unfold patt__) with 100%N].
  Global Existing Instance hyp_map_data_simplify_hyp_val_inst_generated.
  Definition hyp_map_data_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (hyp_map_data_unfold patt__) with 100%N].
  Global Existing Instance hyp_map_data_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [BIT]. *)
  Definition type_of_BIT :=
    fn(∀ i : Z; (i @ (int (i32))); ⌜0 ≤ i < 64⌝)
      → ∃ () : (), ((bf_mask_cons i 1 bf_nil) @ (bitfield_raw (u64))); True.

  (* Specifications for function [GENMASK]. *)
  Definition type_of_GENMASK :=
    fn(∀ (h, l) : Z * Z; (h @ (int (i32))), (l @ (int (i32))); ⌜0 ≤ l⌝ ∗ ⌜l < h < 64⌝)
      → ∃ () : (), ((bf_mask_cons l (h - l + 1) bf_nil) @ (bitfield_raw (u64))); True.

  (* Specifications for function [FIELD_GET]. *)
  Definition type_of_FIELD_GET :=
    fn(∀ (r, a, k, res) : Z * Z * Z * Z; ((bf_mask_cons a k bf_nil) @ (bitfield_raw (u64))), (r @ (bitfield_raw (u64))); ⌜0 ≤ a⌝ ∗ ⌜0 < k⌝ ∗ ⌜a + k ≤ 64⌝ ∗ ⌜normalize_bitfield_eq (bf_slice a k r) res⌝)
      → ∃ () : (), (res @ (int (u64))); True.

  (* Specifications for function [FIELD_PREP]. *)
  Definition type_of_FIELD_PREP :=
    fn(∀ (a, k, v) : Z * Z * Z; ((bf_mask_cons a k bf_nil) @ (bitfield_raw (u64))), (v @ (int (u64))); ⌜0 ≤ a⌝ ∗ ⌜0 < k⌝ ∗ ⌜a + k ≤ 64⌝ ∗ ⌜0 ≤ v < 2^k⌝)
      → ∃ () : (), ((bf_cons a k v bf_nil) @ (bitfield_raw (u64))); True.

  (* Specifications for function [kvm_pte_valid]. *)
  Definition type_of_kvm_pte_valid :=
    fn(∀ pte : Pte; (pte @ (bitfield (Pte))); ⌜bitfield_wf pte⌝)
      → ∃ () : (), ((pte_valid pte) @ (builtin_boolean)); True.

  (* Specifications for function [kvm_pte_table]. *)
  Definition type_of_kvm_pte_table :=
    fn(∀ (pte, level) : Pte * Z; (pte @ (bitfield (Pte))), (level @ (int (u32))); ⌜bitfield_wf pte⌝)
      → ∃ () : (), ((if bool_decide (level = max_level - 1) then false     else if negb (pte_valid pte) then false     else bool_decide (pte_type pte = pte_type_table)) @ (builtin_boolean)); True.

  (* Specifications for function [kvm_set_invalid_pte]. *)
  Definition type_of_kvm_set_invalid_pte :=
    fn(∀ (pte, p) : Pte * loc; (p @ (&own (pte @ (bitfield (Pte))))); ⌜bitfield_wf pte⌝)
      → ∃ () : (), (void); (p ◁ₗ ((pte <| pte_valid := false |>) @ (bitfield (Pte)))).

  (* Specifications for function [kvm_phys_to_pte]. *)
  Definition type_of_kvm_phys_to_pte :=
    fn(∀ pa : Z; (pa @ (int (u64))); True)
      → ∃ () : (), ((mk_pte_addr (addr_of pa)) @ (bitfield (Pte))); True.

  (* Specifications for function [kvm_set_table_pte]. *)
  Definition type_of_kvm_set_table_pte :=
    fn(∀ (p, q, o, pte, va, mm_ops) : loc * loc * loc * Pte * Z * mm_callbacks; (p @ (&own (pte @ (bitfield (Pte))))), (q @ (&own (va @ (int (u64))))), (o @ (&own (mm_ops @ (kvm_pgtable_mm_ops)))); ⌜bitfield_wf pte⌝ ∗ ⌜pte_valid pte⌝)
      → ∃ pa : Z, (void); ⌜mm_ops.(virt_to_phys) va = pa⌝ ∗ (p ◁ₗ ((mk_pte_addr (addr_of pa) <| pte_type := pte_type_table |><| pte_valid := true |>) @ (bitfield (Pte)))).

  (* Specifications for function [kvm_set_valid_leaf_pte]. *)
  Definition type_of_kvm_set_valid_leaf_pte :=
    fn(∀ (p, pte, pa, attr, level, type, pte1) : loc * Pte * Z * Pte * Z * Z * Pte; (p @ (&own (pte @ (bitfield (Pte))))), (pa @ (int (u64))), (attr @ (bitfield (Pte))), (level @ (int (u32))); ⌜bitfield_wf pte⌝ ∗ ⌜bitfield_wf attr⌝ ∗ ⌜type = (if bool_decide (level = max_level - 1) then pte_type_page else pte_type_block)⌝ ∗ ⌜pte1 = mk_pte_addr (addr_of pa) <| pte_valid := true |> <| pte_type := type |><| pte_leaf_attr_lo := pte_leaf_attr_lo attr |> <| pte_leaf_attr_hi := pte_leaf_attr_hi attr |>⌝)
      → ∃ () : (), ((if pte_valid pte then bool_decide (bitfield_repr pte = bitfield_repr pte1) else true) @ (builtin_boolean)); (p ◁ₗ ((if pte_valid pte then pte else pte1) @ (bitfield (Pte)))).

  (* Specifications for function [hyp_map_set_prot_attr]. *)
  Definition type_of_hyp_map_set_prot_attr :=
    fn(∀ (prot, phys, a, attr, mtype, ap, xn, err, mm_ops, o, d) : Prot * Z * Attr * Attr * Z * Z * bool * bool * mm_callbacks * loc * loc; (prot @ (bitfield (Prot))), (d @ (&own (((phys, a, mm_ops, o)) @ (hyp_map_data)))); ⌜bitfield_wf prot⌝ ∗ ⌜mtype = (if prot_device prot then mtype_device else mtype_normal)⌝ ∗ ⌜ap = (if prot_w prot then ap_rw else ap_ro)⌝ ∗ ⌜xn = negb (prot_x prot)⌝ ∗ ⌜err = negb (prot_r prot) || (prot_x prot && (prot_w prot || prot_device prot))⌝ ∗ ⌜attr = {| attr_lo_s1_attridx := mtype; attr_lo_s1_ap := ap; attr_lo_s1_sh := sh_is; attr_lo_s1_af := true; attr_hi_s1_xn := xn |} ⌝)
      → ∃ () : (), ((if err then -err_code else 0) @ (int (i32))); (d ◁ₗ ((if err then (phys, a, mm_ops, o) else (phys, attr, mm_ops, o)) @ (hyp_map_data))).
End spec.

Global Typeclasses Opaque kvm_pgtable_mm_ops_rec.
Global Typeclasses Opaque kvm_pgtable_mm_ops.
Global Typeclasses Opaque hyp_map_data_rec.
Global Typeclasses Opaque hyp_map_data.
