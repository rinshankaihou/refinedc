From iris.program_logic Require Export weakestpre.
From lithium Require Import hooks.
From lithium Require Import all.
From lithium.tutorial Require Import lang notation primitive_laws.
Set Default Proof Using "Type".

(** * Definitions and step *)
Section definitions.
  Context `{!tutorialGS Σ}.

  Definition check_expr (e : expr) (G : val → iProp Σ) : iProp Σ.
  Admitted.
  Class CheckExpr (e : expr) : Type :=
    check_expr_proof G : iProp_to_Prop (check_expr e G).

  Definition check_binop (op : bin_op) (v1 v2 : val) (G : val → iProp Σ) : iProp Σ.
  Admitted.
  Class CheckBinop (op : bin_op) (v1 v2 : val) : Type :=
    check_binop_proof G : iProp_to_Prop (check_binop op v1 v2 G).

  Definition check_if (v : val) (G1 G2 : iProp Σ) : iProp Σ.
  Admitted.
  Class CheckIf (v : val) : Type :=
    check_if_proof G1 G2 : iProp_to_Prop (check_if v G1 G2).
End definitions.

Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | check_expr ?x1 => constr:(CheckExpr x1)
  | check_binop ?x1 ?x2 ?x3 => constr:(CheckBinop x1 x2 x3)
  | check_if ?x1 => constr:(CheckIf x1)
  end.
Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | check_expr ?e ?G =>
      cont uconstr:(((_ : CheckExpr _) _))
  | check_binop ?op ?v1 ?v2 ?G =>
      cont uconstr:(((_ : CheckBinop _ _ _) _))
  | check_if ?v ?G1 ?G2 =>
      cont uconstr:(((_ : CheckIf _) _ _))
  end.

Ltac liToSyntax_hook ::=
  change (check_expr ?x1) with (li.bind1 (check_expr x1));
  change (check_binop ?x1 ?x2 ?x3) with (li.bind1 (check_binop x1 x2 x3)).

Ltac liTStep :=
 liEnsureInvariant;
 first [
 liStep
]; liSimpl.


(** * Tutorial *)

Section proofs.
  Context `{!tutorialGS Σ}.

  (** ** straight line code *)
  Definition main_code : expr :=
    let: "x" := #1 in
    let: "y" := "x" + #1 in
    Assert ("y" = #2).

  Lemma main_code_correct :
    ⊢ [{
      _ ← {check_expr main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma check_expr_Let x e1 e2 G :
    check_expr (Let x e1 e2) G ::=
      v1 ← {check_expr e1};
      v2 ← {check_expr (subst' x v1 e2)};
      return G v2.
  Proof. Admitted.
  Definition check_expr_Let_inst := [instance check_expr_Let].
  Global Existing Instance check_expr_Let_inst | 2.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {check_expr main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma check_expr_val v G :
    check_expr (Val v) G ::= return G v.
  Proof. Admitted.
  Definition check_expr_val_inst := [instance check_expr_val].
  Global Existing Instance check_expr_val_inst.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {check_expr main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma check_expr_binop op e1 e2 G :
    check_expr (BinOp op e1 e2) G ::=
      v1 ← {check_expr e1};
      v2 ← {check_expr e2};
      v  ← {check_binop op v1 v2};
      return G v.
  Proof. Admitted.
  Definition check_expr_binop_inst := [instance check_expr_binop].
  Global Existing Instance check_expr_binop_inst.

  Lemma check_binop_plus_int_int (n1 n2 : Z) G :
    check_binop PlusOp #n1 #n2 G ::=
      return G #(n1 + n2).
  Proof. Admitted.
  Definition check_binop_plus_int_int_inst := [instance check_binop_plus_int_int].
  Global Existing Instance check_binop_plus_int_int_inst.
  Lemma check_binop_minus_int_int (n1 n2 : Z) G :
    check_binop MinusOp #n1 #n2 G ::=
      return G #(n1 - n2).
  Proof. Admitted.
  Definition check_binop_minus_int_int_inst := [instance check_binop_minus_int_int].
  Global Existing Instance check_binop_minus_int_int_inst.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {check_expr main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma check_expr_assert e G :
    check_expr (Assert e) G ::=
      v ← {check_expr e};
      exhale (⌜v = #true⌝);
      return G #0.
  Proof. Admitted.
  Definition check_expr_assert_inst := [instance check_expr_assert].
  Global Existing Instance check_expr_assert_inst.

  Lemma check_binop_eq_int_int (n1 n2 : Z) G :
    check_binop EqOp #n1 #n2 G ::=
      return G #(bool_decide (n1 = n2)).
  Proof. Admitted.
  Definition check_binop_eq_int_int_inst := [instance check_binop_eq_int_int].
  Global Existing Instance check_binop_eq_int_int_inst.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {check_expr main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Qed.

  (** ** function verification *)
  Definition add_one_code : val := λ: "v", "v" + #1.

  Definition fn_spec (v : val) (X : Type)
    (pre : X → val → iProp Σ) (post : X → val → iProp Σ) : iProp Σ.
  Admitted.

  Lemma prove_fn_spec X a e pre post :
    fn_spec (LamV a e) X pre post ::=
      ∀ (x : X) v,
      inhale pre x v;
      v' ← {check_expr (subst' a v e)};
      exhale post x v';
      done.
  Proof. Admitted.

  Lemma add_one_correct :
    ⊢ fn_spec add_one_code Z (λ n v, ⌜v = #n⌝) (λ n v, ⌜v = #(n + 1)⌝).
  Proof.
    iStartProof. iApply prove_fn_spec. simpl.
    repeat liTStep; liShow.
  Qed.

  (** ** using a function *)
  Definition main_param_code (add_one : val) : expr :=
    let: "x" := #1 in
    let: "y" := add_one "x" in
    Assert ("y" = #2).

  Lemma main_param_code_correct add_one :
    ⊢ [{
      inhale fn_spec add_one Z (λ n v, ⌜v = #n⌝) (λ n v, ⌜v = #(n + 1)⌝);
      _ ← {check_expr (main_param_code add_one)};
      done
    }].
  Proof.
    iStartProof. unfold main_param_code.
    repeat liTStep; liShow.
  Abort.

  Lemma check_expr_App e1 e2 G :
    check_expr (App e1 e2) G ::=
      v2 ← {check_expr e2};
      v1 ← {check_expr e1};
      '(existT X (pre, post)) ←
        {find_in_context (FindDirect (λ '(existT X (pre, post)), fn_spec v1 X pre post))};
      ∃ x,
      exhale (pre x v2);
      ∀ v',
      inhale (post x v');
      return G v'.
  Proof. Admitted.
  Definition check_expr_App_inst := [instance check_expr_App].
  Global Existing Instance check_expr_App_inst | 50.

  Lemma main_param_code_correct add_one :
    ⊢ [{
      inhale fn_spec add_one Z (λ n v, ⌜v = #n⌝) (λ n v, ⌜v = #(n + 1)⌝);
      _ ← {check_expr (main_param_code add_one)};
      done
    }].
  Proof.
    iStartProof. unfold main_param_code.
    repeat liTStep; liShow.
  Qed.

  (** ** recursive functions and case distinctions *)
  Definition fib_code : val := rec: "f" "x" :=
      if: "x" = #0 then
        #0
      else if: "x" = #1 then
        #1
      else
         "f" ("x" - #1) + "f" ("x" - #2).

  Lemma prove_fn_spec_rec X f a e pre post :
    fn_spec (RecV f a e) X pre post ::=
      ∀ (x : X) v vr,
      inhale pre x v;
      inhale fn_spec vr X pre post;
      v' ← {check_expr (subst' a v (subst' f vr e))};
      exhale post x v';
      done.
  Proof. Admitted.

  Lemma fib_correct :
    ⊢ fn_spec fib_code unit (λ _ v, ∃ n : Z, ⌜v = #n⌝ ∗ ⌜0 ≤ n⌝)
        (λ _ v, ∃ n' : Z, ⌜v = #n'⌝ ∗ ⌜0 ≤ n'⌝).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.


  Lemma check_expr_if e0 e1 e2 G :
    check_expr (If e0 e1 e2) G ::=
      v ← {check_expr e0};
      {check_if v (check_expr e1 G) (check_expr e2 G)}.
  Proof. Admitted.
  Definition check_expr_if_inst := [instance check_expr_if].
  Global Existing Instance check_expr_if_inst.

  Lemma check_if_bool (b : bool) G1 G2 :
    check_if #b G1 G2 ::=
      and:
      | inhale ⌜b⌝; return G1
      | inhale ⌜¬ b⌝; return G2.
  Proof. Admitted.
  Definition check_if_bool_inst := [instance check_if_bool].
  Global Existing Instance check_if_bool_inst | 2.

  Lemma fib_correct :
    ⊢ fn_spec fib_code unit (λ _ v, ∃ n : Z, ⌜v = #n⌝ ∗ ⌜0 ≤ n⌝)
        (λ _ v, ∃ n' : Z, ⌜v = #n'⌝ ∗ ⌜0 ≤ n'⌝).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Global Instance fn_spec_intro_pers X v pre post :
    IntroPersistent (fn_spec v X pre post) (fn_spec v X pre post).
  Proof. Admitted.

  Lemma fib_correct :
    ⊢ fn_spec fib_code unit (λ _ v, ∃ n : Z, ⌜v = #n⌝ ∗ ⌜0 ≤ n⌝)
        (λ _ v, ∃ n' : Z, ⌜v = #n'⌝ ∗ ⌜0 ≤ n'⌝).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
    Unshelve. all: unshelve_sidecond.
    - lia.
    - lia.
    - lia.
  Qed.

  (** * linked lists *)
  Definition empty_code : val := λ: <>, #NULL.
  Definition is_empty_code : val := λ: "v", "v" = #NULL.
  Definition cons_code : val := λ: "l" "v",
      let: "new_l" := Alloc #2 in
      "new_l" + #0 <- "v";;
      "new_l" + #1 <- "l";;
      "new_l".
  Definition head_code : val := λ: "l", ! ("l" + #0).
  Definition tail_code : val := λ: "l",
      if: "l" = #NULL then #NULL else ! ("l" + #1).
  Definition length_code : val := rec: "f" "l" :=
      if: "l" = #NULL then
        #0
      else
        let: "r" := "f" (! ("l" + #1)) in
        "r" + #1.
  Definition app_code : val := rec: "f" "x" "y" :=
      if: !"x" = #NULL then
        "x" <- "y"
      else
        "f" ((! "x") + #1) "y".

End proofs.
