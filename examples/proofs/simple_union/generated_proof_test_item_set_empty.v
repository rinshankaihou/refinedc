From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import generated_code.
From refinedc.examples.simple_union Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section proof_test_item_set_empty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_item_set_empty]. *)
  Lemma type_test_item_set_empty :
    ⊢ typed_function impl_test_item_set_empty type_of_test_item_set_empty.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_item_set_empty" (i) => arg_i.
    prepare_parameters (i).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_item_set_empty" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_item_set_empty".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_item_set_empty".
  Qed.
End proof_test_item_set_empty.
