From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_init_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_int]. *)
  Lemma type_init_int :
    ⊢ typed_function impl_init_int type_of_init_int.
  Proof.
    Open Scope printing_sugar.
    start_function "init_int" (p) => arg_out.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_int" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_int".
  Qed.
End proof_init_int.
