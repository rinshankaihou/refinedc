From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.pgtable Require Import generated_code.
From refinedc.linux.casestudies.pgtable Require Import generated_spec.
From refinedc.linux.casestudies.pgtable Require Import pgtable_lemmas.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/pgtable.c]. *)
Section proof_FIELD_GET.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [FIELD_GET]. *)
  Lemma type_FIELD_GET (global___builtin_ffsll : loc) :
    global___builtin_ffsll ◁ᵥ global___builtin_ffsll @ function_ptr type_of___builtin_ffsll -∗
    typed_function (impl_FIELD_GET global___builtin_ffsll) type_of_FIELD_GET.
  Proof.
    Local Open Scope printing_sugar.
    start_function "FIELD_GET" ([[[r a] k] res]) => arg__mask arg__reg.
    prepare_parameters (r a k res).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "FIELD_GET" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: unfold normalize_bitfield_eq in *; subst.
    all: try rewrite Z.add_simpl_r Z_least_significant_one_nonempty_mask.
    all: try solve_goal.
    all: try by apply: bf_mask_cons_singleton_nonempty; solve_goal.
    all: try by apply: bf_shr_singleton; solve_goal.
    all: print_sidecondition_goal "FIELD_GET".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "FIELD_GET".
  Qed.
End proof_FIELD_GET.
