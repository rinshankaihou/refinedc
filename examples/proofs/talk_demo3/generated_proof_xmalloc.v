From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo3 Require Import generated_code.
From refinedc.examples.talk_demo3 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section proof_xmalloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [xmalloc]. *)
  Lemma type_xmalloc (global_malloc global_safe_exit : loc) :
    global_malloc ◁ᵥ global_malloc @ function_ptr type_of_malloc -∗
    global_safe_exit ◁ᵥ global_safe_exit @ function_ptr type_of_safe_exit -∗
    typed_function (impl_xmalloc global_malloc global_safe_exit) type_of_xmalloc.
  Proof.
    Local Open Scope printing_sugar.
    start_function "xmalloc" (n) => arg_sz local_p.
    prepare_parameters (n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "xmalloc" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "xmalloc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "xmalloc".
  Qed.
End proof_xmalloc.
