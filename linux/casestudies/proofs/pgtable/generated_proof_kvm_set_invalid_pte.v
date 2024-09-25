From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_kvm_set_invalid_pte.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [kvm_set_invalid_pte]. *)
  Lemma type_kvm_set_invalid_pte (global_BIT : loc) :
    global_BIT ◁ᵥ global_BIT @ function_ptr type_of_BIT -∗
    typed_function (impl_kvm_set_invalid_pte global_BIT) type_of_kvm_set_invalid_pte.
  Proof.
    Local Open Scope printing_sugar.
    start_function "kvm_set_invalid_pte" ([pte p]) => arg_ptep local_pte.
    prepare_parameters (pte p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "kvm_set_invalid_pte" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "kvm_set_invalid_pte".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "kvm_set_invalid_pte".
  Qed.
End proof_kvm_set_invalid_pte.
