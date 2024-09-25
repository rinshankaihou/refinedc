From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_kvm_phys_to_pte.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [kvm_phys_to_pte]. *)
  Lemma type_kvm_phys_to_pte (global_FIELD_PREP global_GENMASK : loc) :
    global_FIELD_PREP ◁ᵥ global_FIELD_PREP @ function_ptr type_of_FIELD_PREP -∗
    global_GENMASK ◁ᵥ global_GENMASK @ function_ptr type_of_GENMASK -∗
    typed_function (impl_kvm_phys_to_pte global_FIELD_PREP global_GENMASK) type_of_kvm_phys_to_pte.
  Proof.
    Local Open Scope printing_sugar.
    start_function "kvm_phys_to_pte" (pa) => arg_pa local_pte.
    prepare_parameters (pa).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "kvm_phys_to_pte" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "kvm_phys_to_pte".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "kvm_phys_to_pte".
  Qed.
End proof_kvm_phys_to_pte.
