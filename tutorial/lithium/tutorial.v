From iris.program_logic Require Export weakestpre.
From lithium Require Import hooks.
From lithium Require Import all.
From lithium.tutorial Require Import lang notation primitive_laws.
Set Default Proof Using "Type".

(** * Definitions of Lithium functions *)
(** First, we define the Lithium functions that we will use later. *)
Section definitions.
  Context `{!tutorialGS Σ}.

  Definition expr_ok (e : expr) (G : val → iProp Σ) : iProp Σ.
  Admitted.

  Definition binop_ok (op : bin_op) (v1 v2 : val) (G : val → iProp Σ) : iProp Σ.
  Admitted.

  Definition unop_ok (op : un_op) (v : val) (G : val → iProp Σ) : iProp Σ.
  Admitted.

  Definition if_ok (v : val) (G1 G2 : iProp Σ) : iProp Σ.
  Admitted.
End definitions.

(** * Boilerplate for setup *)
(** The following code is necessary to register the Lithium functions.
You can ignore it for the purposes of this tutorial. *)
Section setup.
  Context `{!tutorialGS Σ}.

  Class ExprOk (e : expr) : Type :=
    expr_ok_proof G : iProp_to_Prop (expr_ok e G).
  Class BinopOk (op : bin_op) (v1 v2 : val) : Type :=
    binop_ok_proof G : iProp_to_Prop (binop_ok op v1 v2 G).
  Class UnopOk (op : un_op) (v : val) : Type :=
    unop_ok_proof G : iProp_to_Prop (unop_ok op v G).
  Class IfOk (v : val) : Type :=
    if_ok_proof G1 G2 : iProp_to_Prop (if_ok v G1 G2).
End setup.

Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | expr_ok ?x1 => constr:(ExprOk x1)
  | binop_ok ?x1 ?x2 ?x3 => constr:(BinopOk x1 x2 x3)
  | unop_ok ?x1 ?x2 => constr:(UnopOk x1 x2)
  | if_ok ?x1 => constr:(IfOk x1)
  end.
Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | expr_ok ?e ?G =>
      cont uconstr:(((_ : ExprOk _) _))
  | binop_ok ?op ?v1 ?v2 ?G =>
      cont uconstr:(((_ : BinopOk _ _ _) _))
  | unop_ok ?op ?v ?G =>
      cont uconstr:(((_ : UnopOk _ _) _))
  | if_ok ?v ?G1 ?G2 =>
      cont uconstr:(((_ : IfOk _) _ _))
  end.

Ltac liToSyntax_hook ::=
  change (expr_ok ?x1) with (li.bind1 (expr_ok x1));
  change (binop_ok ?x1 ?x2 ?x3) with (li.bind1 (binop_ok x1 x2 x3));
  change (unop_ok ?x1 ?x2) with (li.bind1 (unop_ok x1 x2)).

Ltac liTStep :=
 liEnsureInvariant;
 first [
 liStep
]; liSimpl.


(** * Tutorial *)
(** This is the start of the actual tutorial. *)
Section proofs.
  Context `{!tutorialGS Σ}.

  (*
   Open questions / comments:
   - better name for check? verify? it is some symbolic evaluation?!
     -> changed to _ok (which reads more like a judgement than a function name)
   - better names for exhale and inhale? assert and assume? produce and consume?
     Simon likes assert and assume.
   - highlight that lithium is based on continuation passing style
      - the monad syntax just makes this easier to read
      - this is quite different from other approaches which do a fixed symbolic execution of the program and then mainly focus for cancellation / frame inference
      - somewhere in the thesis, not sure where?
   - can we get rid of the { } on the right of the bind?
   - Youngju: interesting part is find_in_context, there it really starts to look like a custom language with primitives specifically for verification
   - Simon: can probably immediately start with the separation logic part?

   - Simon: should stick with logic programming language and call the expr_ok and friends judgements, instead of programming language and functions
     - TODO: find out what logic programming is and how their judgements look like and what terminology they use
     - maybe call it a logic programming language such that people are not surprised by the extensible function definitions?
     - functions seems like a better name than judgements (or predicates from logic programming) since they have inputs and outputs
     - explain evars somehow
    *)

  (** Framing: Lithium is a logic programming language for building
  automated and foundational separation logic verifiers (proof search
  procedures?)

  Key selling points:
  - language generic
  - automated
  - foundational / proof producing
 *)

  (** ** straight line code *)
  Definition main_code : expr :=
    let: "x" := #1 in
    let: "y" := "x" + #1 in
    Assert ("y" = #2).

  Lemma main_code_correct :
    ⊢ [{
      _ ← {expr_ok main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma expr_ok_Let x e1 e2 G :
    expr_ok (Let x e1 e2) G :-
      v1 ← {expr_ok e1};
      v2 ← {expr_ok (subst' x v1 e2)};
      return G v2.
  Proof. Admitted.
  Definition expr_ok_Let_inst := [instance expr_ok_Let].
  Global Existing Instance expr_ok_Let_inst | 2.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {expr_ok main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma expr_ok_val v G :
    expr_ok (Val v) G :- return G v.
  Proof. Admitted.
  Definition expr_ok_val_inst := [instance expr_ok_val].
  Global Existing Instance expr_ok_val_inst.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {expr_ok main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma expr_ok_binop op e1 e2 G :
    expr_ok (BinOp op e1 e2) G :-
      v1 ← {expr_ok e1};
      v2 ← {expr_ok e2};
      v  ← {binop_ok op v1 v2};
      return G v.
  Proof. Admitted.
  Definition expr_ok_binop_inst := [instance expr_ok_binop].
  Global Existing Instance expr_ok_binop_inst.

  Lemma binop_ok_plus_int_int (n1 n2 : Z) G :
    binop_ok PlusOp #n1 #n2 G :-
      return G #(n1 + n2).
  Proof. Admitted.
  Definition binop_ok_plus_int_int_inst := [instance binop_ok_plus_int_int].
  Global Existing Instance binop_ok_plus_int_int_inst.
  Lemma binop_ok_minus_int_int (n1 n2 : Z) G :
    binop_ok MinusOp #n1 #n2 G :-
      return G #(n1 - n2).
  Proof. Admitted.
  Definition binop_ok_minus_int_int_inst := [instance binop_ok_minus_int_int].
  Global Existing Instance binop_ok_minus_int_int_inst.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {expr_ok main_code};
      done
    }].
  Proof.
    iStartProof. unfold main_code.
    repeat liTStep; liShow.
  Abort.

  Lemma expr_ok_assert e G :
    expr_ok (Assert e) G :-
      v ← {expr_ok e};
      exhale ⌜v = #true⌝;
      return G #0.
  Proof. Admitted.
  Definition expr_ok_assert_inst := [instance expr_ok_assert].
  Global Existing Instance expr_ok_assert_inst.

  Lemma binop_ok_eq_int_int (n1 n2 : Z) G :
    binop_ok EqOp #n1 #n2 G :-
      return G #(bool_decide (n1 = n2)).
  Proof. Admitted.
  Definition binop_ok_eq_int_int_inst := [instance binop_ok_eq_int_int].
  Global Existing Instance binop_ok_eq_int_int_inst.

  Lemma main_code_correct :
    ⊢ [{
      _ ← {expr_ok main_code};
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
    fn_spec (LamV a e) X pre post :-
      ∀ (x : X) v,
      inhale pre x v;
      v' ← {expr_ok (subst' a v e)};
      exhale post x v';
      done.
  Proof.
  Admitted.

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
      _ ← {expr_ok (main_param_code add_one)};
      done
    }].
  Proof.
    iStartProof. unfold main_param_code.
    repeat liTStep; liShow.
  Abort.

  Lemma expr_ok_App e1 e2 G :
    (* TODO: have where `{!TCIsNotVal e1} syntax to add typeclass preconditions *)
    expr_ok (App e1 e2) G  :-
      v2 ← {expr_ok e2};
      v1 ← {expr_ok e1};
     (* TODO: can one have a better notation that does not duplicate
     the pattern? *)
      '(existT X (pre, post)) ←
        find_in_context (FindDirect
             (λ '(existT X (pre, post)), fn_spec v1 X pre post));
      ∃ x,
      exhale (pre x v2);
      ∀ v',
      inhale (post x v');
      return G v'.
  Proof. Admitted.
  Definition expr_ok_App_inst := [instance expr_ok_App].
  Global Existing Instance expr_ok_App_inst | 50.

  Lemma main_param_code_correct add_one :
    ⊢ [{
      inhale fn_spec add_one Z (λ n v, ⌜v = #n⌝) (λ n v, ⌜v = #(n + 1)⌝);
      _ ← {expr_ok (main_param_code add_one)};
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
    fn_spec (RecV f a e) X pre post :-
      ∀ (x : X) v vr,
      inhale pre x v;
      inhale fn_spec vr X pre post;
      v' ← {expr_ok (subst' a v (subst' f vr e))};
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


  Lemma expr_ok_if e0 e1 e2 G :
    expr_ok (If e0 e1 e2) G :-
      v ← {expr_ok e0};
      {if_ok v (expr_ok e1 G) (expr_ok e2 G)}.
  Proof. Admitted.
  Definition expr_ok_if_inst := [instance expr_ok_if].
  Global Existing Instance expr_ok_if_inst.

  Lemma if_ok_0 G1 G2 :
    (* TODO: This is a good usecase for using Typeclass preconditions
    (i.e. showing whether the boolean is provable).*)
    if_ok #0 G1 G2 :- return G2.
  Proof. Admitted.
  Definition if_ok_0_inst := [instance if_ok_0].
  Global Existing Instance if_ok_0_inst | 2.

  Lemma if_ok_1 G1 G2 :
    if_ok #1 G1 G2 :- return G1.
  Proof. Admitted.
  Definition if_ok_1_inst := [instance if_ok_1].
  Global Existing Instance if_ok_1_inst | 2.

  Lemma if_ok_bool (b : bool) G1 G2 :
    if_ok #b G1 G2 :-
      and:
      | inhale ⌜b⌝; return G1
      | inhale ⌜¬ b⌝; return G2.
  Proof. Admitted.
  Definition if_ok_bool_inst := [instance if_ok_bool].
  Global Existing Instance if_ok_bool_inst | 10.

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
    simplify_goal (is_list #NULL xs) G :- exhale ⌜xs = []⌝; return G.
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

  Lemma expr_ok_unop op e G :
    expr_ok (UnOp op e) G :-
      v ← {expr_ok e};
      vr  ← {unop_ok op v};
      return G vr.
  Proof. Admitted.
  Definition expr_ok_unop_inst := [instance expr_ok_unop].
  Global Existing Instance expr_ok_unop_inst.

  Lemma unop_ok_fst v1 v2 G :
    unop_ok FstOp (v1, v2) G :- return G v1.
  Proof. Admitted.
  Definition unop_ok_fst_inst := [instance unop_ok_fst].
  Global Existing Instance unop_ok_fst_inst.
  Lemma unop_ok_snd v1 v2 G :
    unop_ok SndOp (v1, v2) G :- return G v2.
  Proof. Admitted.
  Definition unop_ok_snd_inst := [instance unop_ok_snd].
  Global Existing Instance unop_ok_snd_inst.

  Lemma binop_ok_pair v1 v2 G :
    binop_ok PairOp v1 v2 G :- return G (v1, v2)%V.
  Proof. Admitted.
  Definition binop_ok_pair_inst := [instance binop_ok_pair].
  Global Existing Instance binop_ok_pair_inst.

  Lemma expr_ok_alloc G :
    expr_ok Alloc G :-
      ∀ l : loc,
      inhale (l ↦ #0);
      return G #l.
  Proof. Admitted.
  Definition expr_ok_alloc_inst := [instance expr_ok_alloc].
  Global Existing Instance expr_ok_alloc_inst.

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

  Lemma expr_ok_store e1 e2 G :
    expr_ok (Store e1 e2) G :-
      v2 ← {expr_ok e2};
      v1 ← {expr_ok e1};
      '(l, _) ← find_in_context (FindMapsTo v1);
      inhale (l ↦ v2);
      return G v2.
  Proof. Admitted.
  Definition expr_ok_store_inst := [instance expr_ok_store].
  Global Existing Instance expr_ok_store_inst.

  Lemma expr_ok_load e G :
    expr_ok (Load e) G :-
      v ← {expr_ok e};
      '(l, vl) ← find_in_context (FindMapsTo v);
      inhale (l ↦ vl);
      return G vl.
  Proof. Admitted.
  Definition expr_ok_load_inst := [instance expr_ok_load].
  Global Existing Instance expr_ok_load_inst.

  Lemma cons_correct :
    ⊢ fn_spec cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (v, x)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.


  Lemma find_in_context_find_mapsto_loc (l : loc) G:
    find_in_context (FindMapsTo #l) G :-
      pattern: v, l ↦ v; return G (l, v).
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
    find_in_context (FindList #l) G :-
      pattern: v, l ↦ v; return G (l ↦ v).
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
    subsume (l ↦ v) (is_list #l xs) G :-
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
    find_in_context (FindList v) G :-
      pattern: xs, is_list v xs; return G (is_list v xs).
  Proof. iDestruct 1 as (xs) "[Hl HT]". iExists _. by iFrame. Qed.
  Definition find_in_context_find_list_list_inst :=
    [instance find_in_context_find_list_list with FICSyntactic].
  Global Existing Instance find_in_context_find_list_list_inst | 1.

  Lemma subsume_list_list v xs1 xs2 G :
    subsume (is_list v xs1) (is_list v xs2) G :-
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
    find_in_context (FindMapsTo v) G :-
      pattern: xs, is_list v xs;
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

  Lemma binop_ok_eq_val_NULL v G :
    binop_ok EqOp v #NULL G :-
      o ← find_in_context (FindLocOrNULL v);
      return G #(if o is Some _ then false else true).
  Proof. Admitted.
  Definition binop_ok_eq_val_NULL_inst := [instance binop_ok_eq_val_NULL].
  Global Existing Instance binop_ok_eq_val_NULL_inst.

  Lemma length_correct :
    ⊢ fn_spec length_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs)
      (λ '(va, xs) r, ⌜r = #(length xs)⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_spec_rec. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma find_in_context_find_locornull_list v G:
    find_in_context (FindLocOrNULL v) G :-
      pattern: xs, is_list v xs;
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

End proofs.
