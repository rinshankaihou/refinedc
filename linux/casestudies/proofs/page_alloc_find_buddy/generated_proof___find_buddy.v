From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.page_alloc_find_buddy Require Import generated_code.
From refinedc.linux.casestudies.page_alloc_find_buddy Require Import generated_spec.
From refinedc.linux.casestudies.page_alloc_find_buddy Require Import page_alloc_def.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc_find_buddy.c]. *)
Section proof___find_buddy.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [__find_buddy]. *)
  Lemma type___find_buddy (global___hyp_vmemmap : loc) :
    global_locs !! "__hyp_vmemmap" = Some global___hyp_vmemmap →
    global_initialized_types !! "__hyp_vmemmap" = Some (GT loc (λ 'vmemmap, (vmemmap @ (intptr (u64))) : type)%I) →
    ⊢ typed_function (impl___find_buddy global___hyp_vmemmap) type_of___find_buddy.
  Proof.
    Open Scope printing_sugar.
    start_function "__find_buddy" ([[[[[[[[pool pageloc] page] vmemmap] pages] npages] range_start_idx] order] max_order]) => arg_pool arg_p arg_order local_addr.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "__find_buddy" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: unfold find_buddy, PAGE_SHIFT, PAGE_SIZE in *.
    all: repeat match goal with | H : _ = Lt |- _ => rewrite -/(Z.lt _ _) in H end.
    all: try by etrans; [|done]; rewrite Z.shiftl_mul_pow2 //; lia.
    all: try by rewrite Z.shiftl_mul_pow2 //; etrans; [ apply: Z.mul_le_mono_nonneg_l; [done| ]; apply: (Z.pow_le_mono_r _ _ 11) |].
    all: try by move =>/find_buddy_result_eq; solve_goal.
    all: try by apply: (find_buddy_result' page range_start_idx order npages); solve_goal.
    all: try by apply/find_buddy_result_eq; solve_goal.
    all: print_sidecondition_goal "__find_buddy".
  Qed.
End proof___find_buddy.
