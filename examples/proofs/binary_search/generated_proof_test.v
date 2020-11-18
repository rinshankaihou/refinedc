From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (alloc binary_search compare_int free : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    binary_search ◁ᵥ binary_search @ function_ptr type_of_binary_search -∗
    compare_int ◁ᵥ compare_int @ function_ptr type_of_compare_int -∗
    free ◁ᵥ free @ function_ptr type_of_free -∗
    typed_function (impl_test alloc binary_search compare_int free) type_of_test.
  Proof.
    start_function "test" ([]) => local_res local_ptrs local_needle.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by repeat constructor; lia.
    all: try by apply _.
    all: try by do 4 (destruct x'; [ naive_solver lia |]); exfalso; apply: (H0 3%nat) => //; lia.
    all: print_sidecondition_goal "test".
  Qed.
End proof_test.