From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import generated_code.
From refinedc.tutorial.t02_pointers Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section proof_read_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [read_int]. *)
  Lemma type_read_int :
    ⊢ typed_function impl_read_int type_of_read_int.
  Proof.
    Open Scope printing_sugar.
    start_function "read_int" ([p n]) => arg_a.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "read_int" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "read_int".
  Qed.
End proof_read_int.
