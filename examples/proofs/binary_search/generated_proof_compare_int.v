From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_compare_int.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [compare_int]. *)
  Lemma type_compare_int :
    ⊢ typed_function impl_compare_int type_of_compare_int.
  Proof.
    Local Open Scope printing_sugar.
    start_function "compare_int" ([[[x y] px] py]) => arg_x arg_y local_xi local_yi.
    prepare_parameters (x y px py).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "compare_int" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "compare_int".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "compare_int".
  Qed.
End proof_compare_int.
