From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_init global_is_empty global_member global_pop global_push global_reverse global_talloc global_tfree : loc) :
    global_init ◁ᵥ global_init @ function_ptr type_of_init -∗
    global_is_empty ◁ᵥ global_is_empty @ function_ptr type_of_is_empty -∗
    global_member ◁ᵥ global_member @ function_ptr type_of_member -∗
    global_pop ◁ᵥ global_pop @ function_ptr type_of_pop -∗
    global_push ◁ᵥ global_push @ function_ptr type_of_push -∗
    global_reverse ◁ᵥ global_reverse @ function_ptr type_of_reverse -∗
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    global_tfree ◁ᵥ global_tfree @ function_ptr type_of_tfree -∗
    typed_function (impl_test global_init global_is_empty global_member global_pop global_push global_reverse global_talloc global_tfree) type_of_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test" ([]) => local_list local_elem2 local_elem1 local_elem3.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_unfold; refined_solver.
    all: print_sidecondition_goal "test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test".
  Qed.
End proof_test.
