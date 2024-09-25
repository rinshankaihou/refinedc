From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [test2]. *)
  Definition test2_rec : (unit * Z * Z → type) → (unit * Z * Z → type) := (λ self patt__,
    let x := patt__.1.1 in
    let z := patt__.1.2 in
    let n := patt__.2 in
    struct struct_test2 [@{type}
      (z @ (int (i32))) ;
      (&own (tyexists (λ rfmt__, self (rfmt__, (n), (z)))))
    ]
  )%I.
  Global Typeclasses Opaque test2_rec.

  Global Instance test2_rec_le : TypeMono test2_rec.
  Proof. solve_type_proper. Qed.

  Definition test2 (z : Z) (n : Z) : rtype (unit) := {|
    rty r__ := test2_rec (type_fixpoint test2_rec) (r__, z, n)
  |}.

  Lemma test2_unfold (z : Z) (n : Z) (x : unit):
    (x @ test2 z n)%I ≡@{type} (
      struct struct_test2 [@{type}
        (z @ (int (i32))) ;
        (&own (tyexists (λ rfmt__, rfmt__ @ test2 (n) (z))))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 test2_rec). Qed.

  Definition test2_simplify_hyp_place_inst_generated (z : Z) (n : Z) patt__ :=
    [instance simplify_hyp_place_eq _ _ (test2_unfold (z : Z) (n : Z) patt__) with 100%N].
  Global Existing Instance test2_simplify_hyp_place_inst_generated.
  Definition test2_simplify_goal_place_inst_generated (z : Z) (n : Z) patt__ :=
    [instance simplify_goal_place_eq _ _ (test2_unfold (z : Z) (n : Z) patt__) with 100%N].
  Global Existing Instance test2_simplify_goal_place_inst_generated.

  Definition test2_simplify_hyp_val_inst_generated (z : Z) (n : Z) patt__ :=
    [instance simplify_hyp_val_eq _ _ (test2_unfold (z : Z) (n : Z) patt__) with 100%N].
  Global Existing Instance test2_simplify_hyp_val_inst_generated.
  Definition test2_simplify_goal_val_inst_generated (z : Z) (n : Z) patt__ :=
    [instance simplify_goal_val_eq _ _ (test2_unfold (z : Z) (n : Z) patt__) with 100%N].
  Global Existing Instance test2_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [safe_exit]. *)
  Definition type_of_safe_exit :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜False⌝.

  (* Specifications for function [test1]. *)
  Definition type_of_test1 :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [return1]. *)
  Definition type_of_return1 :=
    fn(∀ () : (); True) → ∃ () : (), ((1) @ (int (i32))); True.

  (* Specifications for function [unreachable]. *)
  Definition type_of_unreachable :=
    fn(∀ () : (); ⌜False⌝) → ∃ () : (), (void); True.

  (* Specifications for function [test_ternary]. *)
  Definition type_of_test_ternary :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [test_assume]. *)
  Definition type_of_test_assume :=
    fn(∀ () : (); ⌜True⌝) → ∃ () : (), (void); True.

  (* Specifications for function [test_bits]. *)
  Definition type_of_test_bits :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [test_comma]. *)
  Definition type_of_test_comma :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.

  (* Specifications for function [inline_global2]. *)
  Definition type_of_inline_global2 :=
    fn(∀ () : (); (initialized "global" ()))
      → ∃ () : (), ((1) @ (int (i32))); True.

  (* Specifications for function [test_logical]. *)
  Definition type_of_test_logical :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [test_not_ptr]. *)
  Definition type_of_test_not_ptr :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [main]. *)
  Definition type_of_main :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.

  (* Specifications for function [test_struct_return]. *)
  Definition type_of_test_struct_return :=
    fn(∀ () : (); True)
      → ∃ n : Z, (struct (struct_test) [@{type} n @ (int (i32)) ]); ⌜n = 1⌝.

  (* Specifications for function [test_fn_params]. *)
  Definition type_of_test_fn_params :=
    fn(∀ spec : (unit → fn_params); (function_ptr (spec)); True)
      → ∃ () : (), (function_ptr (spec)); True.

  (* Specifications for function [test_struct2]. *)
  Definition type_of_test_struct2 :=
    fn(∀ (z, n) : Z * Z; (test2 (z) (n)); True)
      → ∃ () : (), (z @ (int (i32))); True.

  (* Specifications for function [test_reduce]. *)
  Definition type_of_test_reduce :=
    fn(∀ () : (); True) → ∃ () : (), ((0xf1) @ (int (i32))); True.

  (* Specifications for function [test_conditional_annot]. *)
  Definition type_of_test_conditional_annot :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.

  (* Specifications for function [test_rc_assert]. *)
  Definition type_of_test_rc_assert :=
    fn(∀ i : Z; (i @ (int (i32))); True)
      → ∃ () : (), (i @ (int (i32))); True.

  (* Specifications for function [test_manual_exist_arg]. *)
  Definition type_of_test_manual_exist_arg :=
    fn(∀ i : (lvar "k" Z); ((i * 5) @ (int (i32))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [test_manual_exist_arg_client]. *)
  Definition type_of_test_manual_exist_arg_client :=
    fn(∀ () : (); ⌜True⌝) → ∃ () : (), (void); True.

  (* Specifications for function [test_hof]. *)
  Definition type_of_test_hof :=
    fn(∀ () : (); (function_ptr (fn(∀ (l1, l2, n1, n2) : (loc * loc * Z * Z); l1 @ &own (n1 @ int i32), l2 @ &own (n2 @ int i32); True) → ∃ nr : Z, l1 @ &own (place l1); l1 ◁ₗ nr @ int i32 ∗ l2 ◁ₗ n2 @ int i32)); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [test_f]. *)
  Definition type_of_test_f :=
    fn(∀ (l1, n, l2) : loc * Z * loc; (l1 @ (&own (n @ (int (i32))))), (l2 @ (&own (place (l2)))); True)
      → ∃ () : (), (l1 @ (&own ((1) @ (int (i32))))); True.

  (* Specifications for function [test_hof_client]. *)
  Definition type_of_test_hof_client :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜True⌝.

  (* Specifications for function [test_case_printing]. *)
  Definition type_of_test_case_printing :=
    fn(∀ (n, m, o) : Z * Z * (option Z); (n @ (int (i32))), (m @ (int (i32))), ((m = 1) @ (optional (&own (int (i32))) (null))), (o @ (optionalO (λ x,
        &own (x @ (int (i32))) ) (null))); True)
      → ∃ () : (), (void); True.
End spec.

Notation "test2< z , n >" := (test2 z n)
  (only printing, format "'test2<' z ,  n '>'") : printing_sugar.

Global Typeclasses Opaque test2_rec.
Global Typeclasses Opaque test2.
