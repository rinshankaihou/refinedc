From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import code.
From refinedc.examples.reverse Require Import spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (init pop push : loc) :
    init ◁ᵥ init @ function_ptr type_of_init -∗
    pop ◁ᵥ pop @ function_ptr type_of_pop -∗
    push ◁ᵥ push @ function_ptr type_of_push -∗
    typed_function (impl_test init pop push) type_of_test.
  Proof.
    start_function "test" ([]) => local_list local_local1 local_local1_node local_local3 local_local2 local_local4 local_local2_node.
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : loc,
        ∃ l2 : loc,
        ∃ l3 : loc,
        ∃ l4 : loc,
        local_list ◁ₗ uninit LPtr ∗
        local_local3 ◁ₗ uninit LPtr ∗
        local_local4 ◁ₗ uninit LPtr ∗
        local_local1 ◁ₗ (singleton_place (l1)) ∗
        local_local1_node ◁ₗ (singleton_place (l2)) ∗
        local_local2 ◁ₗ (singleton_place (l3)) ∗
        local_local2_node ◁ₗ (singleton_place (l4))
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "test".
  Qed.
End proof_test.
