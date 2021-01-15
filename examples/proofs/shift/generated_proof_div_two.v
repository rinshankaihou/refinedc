From refinedc.typing Require Import typing.
From refinedc.examples.shift Require Import generated_code.
From refinedc.examples.shift Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/shift.c]. *)
Section proof_div_two.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [div_two]. *)
  Lemma type_div_two :
    ⊢ typed_function impl_div_two type_of_div_two.
  Proof.
    Open Scope printing_sugar.
    start_function "div_two" (x) => arg_x.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "div_two" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + by apply Z.shiftr_nonneg.
    + rewrite Z.shiftr_div_pow2 //; lia.
    + rewrite Z.shiftr_div_pow2 //.
    all: print_sidecondition_goal "div_two".
  Qed.
End proof_div_two.
