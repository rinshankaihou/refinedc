From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_kvm_set_table_pte.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [kvm_set_table_pte]. *)
  Lemma type_kvm_set_table_pte (global_BIT global_FIELD_PREP global_kvm_phys_to_pte global_kvm_pte_valid : loc) :
    global_BIT ◁ᵥ global_BIT @ function_ptr type_of_BIT -∗
    global_FIELD_PREP ◁ᵥ global_FIELD_PREP @ function_ptr type_of_FIELD_PREP -∗
    global_kvm_phys_to_pte ◁ᵥ global_kvm_phys_to_pte @ function_ptr type_of_kvm_phys_to_pte -∗
    global_kvm_pte_valid ◁ᵥ global_kvm_pte_valid @ function_ptr type_of_kvm_pte_valid -∗
    typed_function (impl_kvm_set_table_pte global_BIT global_FIELD_PREP global_kvm_phys_to_pte global_kvm_pte_valid) type_of_kvm_set_table_pte.
  Proof.
    Local Open Scope printing_sugar.
    start_function "kvm_set_table_pte" ([[[[[p q] o] pte] va] mm_ops]) => arg_ptep arg_childp arg_mm_ops local_old local_pte.
    prepare_parameters (p q o pte va mm_ops).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "kvm_set_table_pte" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "kvm_set_table_pte".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "kvm_set_table_pte".
  Qed.
End proof_kvm_set_table_pte.
