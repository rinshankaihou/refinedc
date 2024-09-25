From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_binary_search global_compare_int global_free global_xmalloc : loc) :
    global_binary_search ◁ᵥ global_binary_search @ function_ptr type_of_binary_search -∗
    global_compare_int ◁ᵥ global_compare_int @ function_ptr type_of_compare_int -∗
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_xmalloc ◁ᵥ global_xmalloc @ function_ptr type_of_xmalloc -∗
    typed_function (impl_test global_binary_search global_compare_int global_free global_xmalloc) type_of_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test" ([]) => local_res local_ptrs local_needle.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by repeat constructor; lia.
    all: try by apply _.
    all: try by do 4 (destruct x'; [ naive_solver lia |]); exfalso; apply: (H0 3%nat) => //; lia.
    all: print_sidecondition_goal "test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test".
  Qed.
End proof_test.
