From iris.program_logic Require Export weakestpre.
From lithium Require Import hooks.
From lithium Require Import all.
From lithium.tutorial Require Import lang notation primitive_laws.
Set Default Proof Using "Type".

(** * Definitions and setup *)
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

  Definition check_unop (op : un_op) (v : val) (G : val → iProp Σ) : iProp Σ.
  Admitted.
  Class CheckUnop (op : un_op) (v : val) : Type :=
    check_unop_proof G : iProp_to_Prop (check_unop op v G).

  Definition check_if (v : val) (G1 G2 : iProp Σ) : iProp Σ.
  Admitted.
  Class CheckIf (v : val) : Type :=
    check_if_proof G1 G2 : iProp_to_Prop (check_if v G1 G2).
End definitions.

Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | check_expr ?x1 => constr:(CheckExpr x1)
  | check_binop ?x1 ?x2 ?x3 => constr:(CheckBinop x1 x2 x3)
  | check_unop ?x1 ?x2 => constr:(CheckUnop x1 x2)
  | check_if ?x1 => constr:(CheckIf x1)
  end.
Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | check_expr ?e ?G =>
      cont uconstr:(((_ : CheckExpr _) _))
  | check_binop ?op ?v1 ?v2 ?G =>
      cont uconstr:(((_ : CheckBinop _ _ _) _))
  | check_unop ?op ?v ?G =>
      cont uconstr:(((_ : CheckUnop _ _) _))
  | check_if ?v ?G1 ?G2 =>
      cont uconstr:(((_ : CheckIf _) _ _))
  end.

Ltac liToSyntax_hook ::=
  change (check_expr ?x1) with (li.bind1 (check_expr x1));
  change (check_binop ?x1 ?x2 ?x3) with (li.bind1 (check_binop x1 x2 x3));
  change (check_unop ?x1 ?x2) with (li.bind1 (check_unop x1 x2)).

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

  Lemma check_if_0 G1 G2 :
    check_if #0 G1 G2 ::= return G2.
  Proof. Admitted.
  Definition check_if_0_inst := [instance check_if_0].
  Global Existing Instance check_if_0_inst | 2.

  Lemma check_if_1 G1 G2 :
    check_if #1 G1 G2 ::= return G1.
  Proof. Admitted.
  Definition check_if_1_inst := [instance check_if_1].
  Global Existing Instance check_if_1_inst | 2.

  Lemma check_if_bool (b : bool) G1 G2 :
    check_if #b G1 G2 ::=
      and:
      | inhale ⌜b⌝; return G1
      | inhale ⌜¬ b⌝; return G2.
  Proof. Admitted.
  Definition check_if_bool_inst := [instance check_if_bool].
  Global Existing Instance check_if_bool_inst | 10.

  Lemma fib_correct :
    ⊢ fn_spec fib_code unit (λ _ v, ∃ n : Z, ⌜v = #n⌝ ∗ ⌜0 ≤ n⌝)
        (λ _ v, ∃ n' : Z, ⌜v = #n'⌝ ∗ ⌜0 ≤ n'⌝).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Global Instance fn_spec_pers X v pre post :
    Persistent (fn_spec v X pre post).
  Proof. Admitted.

  Global Instance fn_spec_intro_pers X v pre post :
    IntroPersistent (fn_spec v X pre post) (fn_spec v X pre post).
  Proof. constructor. by iIntros "#?". Qed.

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
  (** ** constructing linked lists *)
  Definition empty_code : val := λ: <>, #NULL.
  Definition cons_code : val := λ: "a",
      let: "l" := Fst "a" in
      let: "v" := Snd "a" in
      let: "new_l" := Alloc in
      "new_l" <- ("l", "v");;
      "new_l".

  Definition build_list_code (empty cons : val) : val := λ: <>,
    let: "l" := empty #0 in
    let: "l" := cons ("l", #1) in
    let: "l" := cons ("l", #2) in
    "l".

  Fixpoint is_list (v : val) (xs : list val) : iProp Σ :=
    match xs with
    | [] => ⌜v = #NULL⌝
    | x :: xs => ∃ (l : loc) vnext, ⌜v = #l⌝ ∗ l ↦ (vnext, x)%V ∗ is_list vnext xs
  end.
  Global Typeclasses Opaque is_list.
  Global Opaque is_list.

  Lemma empty_correct :
    ⊢ fn_spec empty_code unit (λ _ _, True) (λ _ v, is_list v []).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma simplify_goal_is_list_null xs G :
    simplify_goal (is_list #NULL xs) G ::= exhale ⌜xs = []⌝; return G.
  Proof. Admitted.
  Definition simplify_goal_is_list_null_inst := [instance simplify_goal_is_list_null with 50%N].
  Global Existing Instance simplify_goal_is_list_null_inst.

  Lemma empty_correct :
    ⊢ fn_spec empty_code unit (λ _ _, True) (λ _ v, is_list v []).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Qed.


  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma check_expr_unop op e G :
    check_expr (UnOp op e) G ::=
      v ← {check_expr e};
      vr  ← {check_unop op v};
      return G vr.
  Proof. Admitted.
  Definition check_expr_unop_inst := [instance check_expr_unop].
  Global Existing Instance check_expr_unop_inst.

  Lemma check_unop_fst v1 v2 G :
    check_unop FstOp (v1, v2) G ::= return G v1.
  Proof. Admitted.
  Definition check_unop_fst_inst := [instance check_unop_fst].
  Global Existing Instance check_unop_fst_inst.
  Lemma check_unop_snd v1 v2 G :
    check_unop SndOp (v1, v2) G ::= return G v2.
  Proof. Admitted.
  Definition check_unop_snd_inst := [instance check_unop_snd].
  Global Existing Instance check_unop_snd_inst.

  Lemma check_binop_pair v1 v2 G :
    check_binop PairOp v1 v2 G ::= return G (v1, v2)%V.
  Proof. Admitted.
  Definition check_binop_pair_inst := [instance check_binop_pair].
  Global Existing Instance check_binop_pair_inst.

  Lemma check_expr_alloc G :
    check_expr Alloc G ::=
      ∀ l : loc,
      inhale (l ↦ #0);
      return G #l.
  Proof. Admitted.
  Definition check_expr_alloc_inst := [instance check_expr_alloc].
  Global Existing Instance check_expr_alloc_inst.

  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Definition FindMapsTo (v : val) :=
  {| fic_A := (loc * val); fic_Prop '(l, vr) := (⌜v = #l⌝ ∗ l ↦ vr)%I; |}.
  Global Typeclasses Opaque FindMapsTo.

  Lemma check_expr_store e1 e2 G :
    check_expr (Store e1 e2) G ::=
      v2 ← {check_expr e2};
      v1 ← {check_expr e1};
      '(l, _) ← {find_in_context (FindMapsTo v1)};
      inhale (l ↦ v2);
      return G v2.
  Proof. Admitted.
  Definition check_expr_store_inst := [instance check_expr_store].
  Global Existing Instance check_expr_store_inst.

  Lemma check_expr_load e G :
    check_expr (Load e) G ::=
      v ← {check_expr e};
      '(l, vl) ← {find_in_context (FindMapsTo v)};
      inhale (l ↦ vl);
      return G vl.
  Proof. Admitted.
  Definition check_expr_load_inst := [instance check_expr_load].
  Global Existing Instance check_expr_load_inst.

  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma find_in_context_find_mapsto_loc (l : loc) G:
    find_in_context (FindMapsTo #l) G ::=
      ∃ v,
      exhale (l ↦ v);
      return G (l, v).
  Proof. iDestruct 1 as (v) "[Hl HT]". iExists (_, _) => /=. by iFrame. Qed.
  Definition find_in_context_find_mapsto_loc_inst :=
    [instance find_in_context_find_mapsto_loc with FICSyntactic].
  Global Existing Instance find_in_context_find_mapsto_loc_inst | 1.

  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Definition FindList (v : val) :=
  {| fic_A := iProp Σ; fic_Prop P := P; |}.
  Global Typeclasses Opaque FindList.
  Lemma find_in_context_find_list_loc (l : loc) G:
    find_in_context (FindList #l) G ::=
      ∃ v, exhale l ↦ v; return G (l ↦ v).
  Proof. iDestruct 1 as (v) "[Hl HT]". iExists _. by iFrame. Qed.
  Definition find_in_context_find_list_loc_inst :=
    [instance find_in_context_find_list_loc with FICSyntactic].
  Global Existing Instance find_in_context_find_list_loc_inst | 10.

  Global Instance related_to_list v xs : RelatedTo (is_list v xs) | 100 := {| rt_fic := FindList v |}.

  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma subsume_mapsto_list (l : loc) v xs G :
    subsume (l ↦ v) (is_list #l xs) G ::=
     ∃ v1 v2 xs',
     exhale ⌜v = (v1, v2)%V⌝ ∗ ⌜xs = v2 :: xs'⌝ ∗ is_list v1 xs';
     return G.
  Proof. Admitted.
  Definition subsume_mapsto_list_inst := [instance subsume_mapsto_list].
  Global Existing Instance subsume_mapsto_list_inst.

  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Qed.

  Lemma build_list_correct empty cons :
    fn_spec empty unit (λ _ _, True) (λ _ v, is_list v []) -∗
    fn_spec cons (val * list val) (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs) (λ '(x, xs) r, is_list r (x :: xs)) -∗
    fn_spec (build_list_code empty cons) unit (λ _ _, True) (λ _ v, is_list v [ #1; #2 ]).
  Proof.
    iStartProof. iIntros "#? #?". iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma find_in_context_find_list_list v G:
    find_in_context (FindList v) G ::=
      ∃ xs, exhale is_list v xs; return G (is_list v xs).
  Proof. iDestruct 1 as (xs) "[Hl HT]". iExists _. by iFrame. Qed.
  Definition find_in_context_find_list_list_inst :=
    [instance find_in_context_find_list_list with FICSyntactic].
  Global Existing Instance find_in_context_find_list_list_inst | 1.

  Lemma subsume_list_list v xs1 xs2 G :
    subsume (is_list v xs1) (is_list v xs2) G ::=
     exhale ⌜xs1 = xs2⌝;
     return G.
  Proof. Admitted.
  Definition subsume_list_list_inst := [instance subsume_list_list].
  Global Existing Instance subsume_list_list_inst.


  Lemma build_list_correct empty cons :
    fn_spec empty unit (λ _ _, True) (λ _ v, is_list v []) -∗
    fn_spec cons (val * list val) (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs) (λ '(x, xs) r, is_list r (x :: xs)) -∗
    fn_spec (build_list_code empty cons) unit (λ _ _, True) (λ _ v, is_list v [ #2; #1 ]).
  Proof.
    iStartProof. iIntros "#? #?". iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Qed.

  (** ** destructing linked lists *)
  Definition head_code : val := λ: "l", Snd (! "l").

  Lemma head_correct :
    ⊢ fn_spec head_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs ∗ ⌜0 < length xs⌝)
      (λ '(va, xs) r, ⌜∃ xs', xs = r::xs'⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma find_in_context_find_mapsto_list v G:
    find_in_context (FindMapsTo v) G ::=
      ∃ xs, exhale is_list v xs;
      exhale ⌜0 < length xs⌝;
      ∀ (l : loc) v' x xs',
      inhale ⌜v = #l⌝ ∗ ⌜xs = x::xs'⌝ ∗ is_list v' xs';
      return G (l, (v', x)%V).
  Proof. Admitted.
  Definition find_in_context_find_mapsto_list_inst :=
    [instance find_in_context_find_mapsto_list with FICSyntactic].
  Global Existing Instance find_in_context_find_mapsto_list_inst | 10.

  Lemma head_correct :
    ⊢ fn_spec head_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs ∗ ⌜0 < length xs⌝)
      (λ '(va, xs) r, ⌜∃ xs', xs = r::xs'⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
    Unshelve. all: unshelve_sidecond.
    - naive_solver.
  Qed.



  Definition length_code : val := rec: "f" "l" :=
      if: "l" = #NULL then
        #0
      else
        let: "r" := "f" (Fst (! "l")) in
        "r" + #1.

  Lemma length_correct :
    ⊢ fn_spec length_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs)
      (λ '(va, xs) r, ⌜r = #(length xs)⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  (* TODO: mention that there are also other approaches to handle this
  overloading, see RefinedC and Islaris *)
  Definition FindLocOrNULL (v : val) :=
  {| fic_A := option loc; fic_Prop o :=
      match o with | Some l => ⌜v = #l⌝ | None => ⌜v = #NULL⌝ end%I : iProp Σ; |}.
  Global Typeclasses Opaque FindLocOrNULL.

  Lemma check_binop_eq_val_NULL v G :
    check_binop EqOp v #NULL G ::=
      o ← {find_in_context (FindLocOrNULL v)};
      return G #(if o is Some _ then false else true).
  Proof. Admitted.
  Definition check_binop_eq_val_NULL_inst := [instance check_binop_eq_val_NULL].
  Global Existing Instance check_binop_eq_val_NULL_inst.

  Lemma length_correct :
    ⊢ fn_spec length_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs)
      (λ '(va, xs) r, ⌜r = #(length xs)⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma find_in_context_find_locornull_list v G:
    find_in_context (FindLocOrNULL v) G ::=
      ∃ xs, exhale is_list v xs;
      and:
      | inhale ⌜xs = []⌝ ∗ ⌜v = #NULL⌝; return G None
      | ∀ (l : loc) v' x xs',
        inhale ⌜v = #l⌝ ∗ ⌜xs = x::xs'⌝ ∗ l ↦ (v', x)%V ∗ is_list v' xs';
        return G (Some l).
  Proof. Admitted.
  Definition find_in_context_find_locornull_list_inst :=
    [instance find_in_context_find_locornull_list with FICSyntactic].
  Global Existing Instance find_in_context_find_locornull_list_inst | 10.

  Lemma length_correct :
    ⊢ fn_spec length_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs)
      (λ '(va, xs) r, ⌜r = #(length xs)⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
    Unshelve. all: unshelve_sidecond.
    - do 2 f_equal. lia.
  Qed.

  (* TODOs:
     - explain evars somehow
 *)

End proofs.
