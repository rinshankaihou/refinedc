From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_set_green.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [set_green]. *)
  Lemma type_set_green :
    ⊢ typed_function impl_set_green type_of_set_green.
  Proof.
    Open Scope printing_sugar.
    start_function "set_green" ([[p c] g]) => arg_c arg_g.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "set_green" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "set_green".
  Qed.
End proof_set_green.