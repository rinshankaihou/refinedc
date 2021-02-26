From refinedc.typing Require Import typing.
From refinedc.examples.quick_sort Require Import generated_code.
From refinedc.examples.quick_sort Require Import quick_sort_lemmas.
Set Default Proof Using "Type".

(* Generated from [examples/quick_sort.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [partition]. *)
  Definition type_of_partition :=
    fn(∀ (a, es, lo, hi) : loc * (list Z) * nat * nat; (a @ (&own (array (i32) (es `at_type` (int i32))))), (lo @ (int (i32))), (hi @ (int (i32))); ⌜es <> []⌝ ∗ ⌜lo < hi⌝ ∗ ⌜hi < length es⌝)
      → ∃ (index, pivot, xs) : nat * Z * (list Z), (index @ (int (i32))); ⌜lo <= index⌝ ∗ ⌜index <= hi⌝ ∗ (a ◁ₗ (array (i32) (xs `at_type` (int i32)))) ∗ ⌜unchanged lo hi xs es⌝ ∗ ⌜Permutation xs es⌝ ∗ ⌜xs !! index = Some pivot⌝ ∗ ⌜partitioned lo index index hi pivot xs⌝.

  (* Specifications for function [qsort]. *)
  Definition type_of_qsort :=
    fn(∀ (a, es, lo, hi) : loc * (list Z) * Z * Z; (a @ (&own (array (i32) (es `at_type` (int i32))))), (lo @ (int (i32))), (hi @ (int (i32))); ⌜lo >= 0⌝ ∗ ⌜hi < length es⌝ ∗ ⌜length es <= max_int i32⌝)
      → ∃ xs : (list Z), (void); (a ◁ₗ (array (i32) (xs `at_type` (int i32)))) ∗ ⌜unchanged lo hi xs es⌝ ∗ ⌜Permutation xs es⌝ ∗ ⌜sorted lo hi xs⌝.
End spec.
