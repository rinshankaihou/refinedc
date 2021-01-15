From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_pop.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [pop]. *)
  Lemma type_pop (global_free : loc) :
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    typed_function (impl_pop global_free) type_of_pop.
  Proof.
    Open Scope printing_sugar.
    start_function "pop" ([l p]) => arg_p local_node local_ret.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "pop" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "pop".
  Qed.
End proof_pop.
