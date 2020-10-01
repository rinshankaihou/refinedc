From refinedc.typing Require Import typing.
From refinedc.tutorial.t07_arrays Require Import generated_code.
From refinedc.tutorial.t07_arrays Require Import generated_spec.
From refinedc.tutorial.t07_arrays Require Import t07_arrays_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t07_arrays.c]. *)
Section proof_permute.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [permute]. *)
  Lemma type_permute :
    ⊢ typed_function impl_permute type_of_permute.
  Proof.
    start_function "permute" ([[[[[ar elts] i] j] v1] v2]) => arg_ar arg_i arg_j local_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "permute" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "permute".
  Qed.
End proof_permute.
