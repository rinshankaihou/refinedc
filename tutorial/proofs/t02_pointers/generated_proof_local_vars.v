From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import generated_code.
From refinedc.tutorial.t02_pointers Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section proof_local_vars.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [local_vars]. *)
  Lemma type_local_vars :
    ⊢ typed_function impl_local_vars type_of_local_vars.
  Proof.
    start_function "local_vars" ([]) => arg_b local_var local_dummy local_p.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "local_vars" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "local_vars".
  Qed.
End proof_local_vars.
