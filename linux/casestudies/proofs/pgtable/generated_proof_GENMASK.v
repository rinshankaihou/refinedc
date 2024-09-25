From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_GENMASK.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [GENMASK]. *)
  Lemma type_GENMASK :
    ⊢ typed_function impl_GENMASK type_of_GENMASK.
  Proof.
    Local Open Scope printing_sugar.
    start_function "GENMASK" ([h l]) => arg_h arg_l.
    prepare_parameters (h l).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "GENMASK" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: have [??] : 1 ≤ 1 ≪ l ≤ 2^64 - 1 by apply Z_shiftl_1_range; solve_goal.
    all: try have -> : max_int u64 = 2^64 - 1 by solve_goal.
    all: try have -> : ly_size i64 * 8 = bits_per_int u64 by solve_goal.
    all: try have -> : bits_per_int u64 = 64 by solve_goal.
    all: try have -> : Z_lunot 64 0 = 2^64 - 1 by solve_goal.
    all: try solve_goal.
    all: try by apply: bf_mask_gen; solve_goal.
    all: print_sidecondition_goal "GENMASK".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "GENMASK".
  Qed.
End proof_GENMASK.
