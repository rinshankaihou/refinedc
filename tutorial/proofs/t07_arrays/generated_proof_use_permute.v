From refinedc.typing Require Import typing.
From refinedc.tutorial.t07_arrays Require Import generated_code.
From refinedc.tutorial.t07_arrays Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t07_arrays Require Import t07_arrays_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t07_arrays.c]. *)
Section proof_use_permute.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [use_permute]. *)
  Lemma type_use_permute (global_permute : loc) :
    global_permute ◁ᵥ global_permute @ function_ptr type_of_permute -∗
    typed_function (impl_use_permute global_permute) type_of_use_permute.
  Proof.
    Local Open Scope printing_sugar.
    start_function "use_permute" ([[ar elts] n]) => arg_ar arg_n.
    prepare_parameters (ar elts n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "use_permute" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "use_permute".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "use_permute".
  Qed.
End proof_use_permute.
