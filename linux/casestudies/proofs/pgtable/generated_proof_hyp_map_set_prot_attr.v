From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_hyp_map_set_prot_attr.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [hyp_map_set_prot_attr]. *)
  Lemma type_hyp_map_set_prot_attr (global_BIT global_FIELD_PREP global_GENMASK : loc) :
    global_BIT ◁ᵥ global_BIT @ function_ptr type_of_BIT -∗
    global_FIELD_PREP ◁ᵥ global_FIELD_PREP @ function_ptr type_of_FIELD_PREP -∗
    global_GENMASK ◁ᵥ global_GENMASK @ function_ptr type_of_GENMASK -∗
    typed_function (impl_hyp_map_set_prot_attr global_BIT global_FIELD_PREP global_GENMASK) type_of_hyp_map_set_prot_attr.
  Proof.
    Local Open Scope printing_sugar.
    start_function "hyp_map_set_prot_attr" ([[[[[[[[[[prot phys] a] attr] mtype] ap] xn] err] mm_ops] o] d]) => arg_prot arg_data local_mtype local_sh local_ap local_attr local_device.
    prepare_parameters (prot phys a attr mtype ap xn err mm_ops o d).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "hyp_map_set_prot_attr" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "hyp_map_set_prot_attr".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "hyp_map_set_prot_attr".
  Qed.
End proof_hyp_map_set_prot_attr.
