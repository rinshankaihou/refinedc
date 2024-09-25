From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_talloc_array.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [talloc_array]. *)
  Lemma type_talloc_array (global_talloc : loc) :
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    typed_function (impl_talloc_array global_talloc) type_of_talloc_array.
  Proof.
    Local Open Scope printing_sugar.
    start_function "talloc_array" ([size n]) => arg_size arg_n.
    prepare_parameters (size n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "talloc_array" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by rewrite /layout_wf -Z.mod_divide // /ly_size/ly_align/=; nia.
    all: print_sidecondition_goal "talloc_array".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "talloc_array".
  Qed.
End proof_talloc_array.
