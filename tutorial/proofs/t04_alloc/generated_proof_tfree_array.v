From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_tfree_array.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [tfree_array]. *)
  Lemma type_tfree_array (global_tfree : loc) :
    global_tfree ◁ᵥ global_tfree @ function_ptr type_of_tfree -∗
    typed_function (impl_tfree_array global_tfree) type_of_tfree_array.
  Proof.
    Local Open Scope printing_sugar.
    start_function "tfree_array" ([size n]) => arg_size arg_n arg_ptr.
    prepare_parameters (size n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tfree_array" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by rewrite /layout_wf -Z.mod_divide // /ly_size/ly_align/=; nia.
    all: print_sidecondition_goal "tfree_array".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "tfree_array".
  Qed.
End proof_tfree_array.
