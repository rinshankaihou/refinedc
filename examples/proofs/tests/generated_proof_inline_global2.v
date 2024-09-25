From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_inline_global2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [inline_global2]. *)
  Lemma type_inline_global2 (global_global global_inline_global1 : loc) :
    global_locs !! "global" = Some global_global →
    global_initialized_types !! "global" = Some (GT (()) (λ '(), ((1) @ (int (i32))) : type)%I) →
    global_inline_global1 ◁ᵥ global_inline_global1 @ inline_function_ptr (impl_inline_global1 global_global) -∗
    typed_function (impl_inline_global2 global_inline_global1) type_of_inline_global2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "inline_global2" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "inline_global2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "inline_global2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "inline_global2".
  Qed.
End proof_inline_global2.
