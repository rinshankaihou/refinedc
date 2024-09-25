From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_kvm_pte_table.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [kvm_pte_table]. *)
  Lemma type_kvm_pte_table (global_BIT global_FIELD_GET global_kvm_pte_valid : loc) :
    global_BIT ◁ᵥ global_BIT @ function_ptr type_of_BIT -∗
    global_FIELD_GET ◁ᵥ global_FIELD_GET @ function_ptr type_of_FIELD_GET -∗
    global_kvm_pte_valid ◁ᵥ global_kvm_pte_valid @ function_ptr type_of_kvm_pte_valid -∗
    typed_function (impl_kvm_pte_table global_BIT global_FIELD_GET global_kvm_pte_valid) type_of_kvm_pte_table.
  Proof.
    Local Open Scope printing_sugar.
    start_function "kvm_pte_table" ([pte level]) => arg_pte arg_level.
    prepare_parameters (pte level).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "kvm_pte_table" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "kvm_pte_table".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "kvm_pte_table".
  Qed.
End proof_kvm_pte_table.
