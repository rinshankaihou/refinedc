From refinedc.typing Require Import typing.
From refinedc.tutorial.t07_arrays Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t07_arrays Require Import t07_arrays_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t07_arrays.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [permute]. *)
  Definition type_of_permute :=
    fn(∀ (ar, elts, i, j, v1, v2) : loc * (list Z) * nat * nat * Z * Z; (ar @ (&own (array (i32) (elts `at_type` (int i32))))), (i @ (int (i32))), (j @ (int (i32))); ⌜elts !! i = Some v1⌝ ∗ ⌜elts !! j = Some v2⌝ ∗ ⌜i ≠ j⌝)
      → ∃ () : (), (void); (ar ◁ₗ (array (i32) (<[j:=v1]>(<[i:=v2]>elts) `at_type` (int i32)))).

  (* Specifications for function [use_permute]. *)
  Definition type_of_use_permute :=
    fn(∀ (ar, elts, n) : loc * (list Z) * nat; (ar @ (&own (array (i32) (elts `at_type` (int i32))))), (n @ (int (i32))); ⌜2 < length elts⌝)
      → ∃ () : (), (void); (ar ◁ₗ (array (i32) (elts `at_type` (int i32)))).

  (* Specifications for function [min_array]. *)
  Definition type_of_min_array :=
    fn(∀ (ar, elts, n) : loc * (list Z) * nat; (ar @ (&own (array (i32) (elts `at_type` (int i32))))), (n @ (int (i32))); ⌜(n ≤ length elts)%nat⌝)
      → ∃ () : (), ((n ≠ 0%nat) @ (optional (∃ₜ i : nat, constrained (i @ (int (i32))) ⌜index_of_min_list_Z (take n elts) i⌝) ((-1) @ (int (i32))))); (ar ◁ₗ (array (i32) (elts `at_type` (int i32)))).
End spec.
