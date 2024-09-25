From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_pop.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [pop]. *)
  Lemma type_pop (global_tfree : loc) :
    global_tfree ◁ᵥ global_tfree @ function_ptr type_of_tfree -∗
    typed_function (impl_pop global_tfree) type_of_pop.
  Proof.
    Local Open Scope printing_sugar.
    start_function "pop" ([l p]) => arg_p local_node local_ret.
    prepare_parameters (l p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "pop" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "pop".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "pop".
  Qed.
End proof_pop.
