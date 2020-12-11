From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import generated_code.
From refinedc.tutorial.t02_pointers Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section proof_use_read_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [use_read_int]. *)
  Lemma type_use_read_int (global_read_int : loc) :
    global_read_int ◁ᵥ global_read_int @ function_ptr type_of_read_int -∗
    typed_function (impl_use_read_int global_read_int) type_of_use_read_int.
  Proof.
    start_function "use_read_int" ([]) => local_local local_read.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "use_read_int" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "use_read_int".
  Qed.
End proof_use_read_int.
