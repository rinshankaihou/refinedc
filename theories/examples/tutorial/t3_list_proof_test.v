From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t3_list_code.
From refinedc.examples.tutorial Require Import t3_list_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t3_list.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (alloc free init is_empty push pop reverse member : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    free ◁ᵥ free @ function_ptr type_of_free -∗
    init ◁ᵥ init @ function_ptr type_of_init -∗
    is_empty ◁ᵥ is_empty @ function_ptr type_of_is_empty -∗
    push ◁ᵥ push @ function_ptr type_of_push -∗
    pop ◁ᵥ pop @ function_ptr type_of_pop -∗
    reverse ◁ᵥ reverse @ function_ptr type_of_reverse -∗
    member ◁ᵥ member @ function_ptr type_of_member -∗
    typed_function (impl_test alloc free init is_empty push pop reverse member) type_of_test.
  Proof.
    start_function "test" ([]) => local_list local_elem2 local_elem1 local_elem3.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by set_unfold; refined_solver.
    all: print_sidecondition_goal "test".
  Qed.
End proof_test.
