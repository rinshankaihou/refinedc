From lithium Require Export base.
From lithium Require Import definitions hooks.

Import environments.

Module li.
Section lithium.
  Context {Σ : gFunctors}.

  (* Alternative names: prove, assert, consume *)
  Definition exhale (P T : iProp Σ) : iProp Σ :=
    P ∗ T.

  (* Alternative names: intro, assume, produce *)
  Definition inhale (P T : iProp Σ) : iProp Σ :=
    P -∗ T.

  Definition all {A} : (A → iProp Σ) → iProp Σ :=
    bi_forall.

  Definition exist {A} : (A → iProp Σ) → iProp Σ :=
    bi_exist.

  Definition done : iProp Σ := True.

  Definition false : iProp Σ := False.

  Definition bind0 (P : iProp Σ → iProp Σ) (T : iProp Σ) : iProp Σ := P T.
  Definition bind1 {A1} (P : (A1 → iProp Σ) → iProp Σ) (T : A1 → iProp Σ) : iProp Σ := P T.
  Definition bind2 {A1 A2} (P : (A1 → A2 → iProp Σ) → iProp Σ) (T : A1 → A2 → iProp Σ) : iProp Σ := P T.
  Definition bind3 {A1 A2 A3} (P : (A1 → A2 → A3 → iProp Σ) → iProp Σ) (T : A1 → A2 → A3 → iProp Σ) : iProp Σ := P T.
  Definition bind4 {A1 A2 A3 A4} (P : (A1 → A2 → A3 → A4 → iProp Σ) → iProp Σ) (T : A1 → A2 → A3 → A4 → iProp Σ) : iProp Σ := P T.
  Definition bind5 {A1 A2 A3 A4 A5} (P : (A1 → A2 → A3 → A4 → A5 → iProp Σ) → iProp Σ) (T : A1 → A2 → A3 → A4 → A5 → iProp Σ) : iProp Σ := P T.
End lithium.
End li.

Declare Scope lithium_scope.
Delimit Scope lithium_scope with LI.
Global Open Scope lithium_scope.

Declare Custom Entry lithium.

Notation "'[{' e } ]" := e
  (e custom lithium at level 200,
    format "'[hv' [{  '[hv' e ']'  '/' } ] ']'") : lithium_scope.
Notation "{ x }" := x (in custom lithium, x constr).

Notation "'inhale' x" := (li.inhale x) (in custom lithium at level 0, x constr,
                           format "'inhale'  '[' x ']'") : lithium_scope.
Notation "'exhale' x" := (li.exhale x) (in custom lithium at level 0, x constr,
                           format "'exhale'  '[' x ']'") : lithium_scope.
Notation "'done'" := (li.done) (in custom lithium at level 0) : lithium_scope.
Notation "'false'" := (li.false) (in custom lithium at level 0) : lithium_scope.
(* Notation "x !" := (exhale_opt x) (at level 100, format "x !") : lithium_scope. *)
Notation "∀ x .. y , P" := (li.all (λ x, .. (li.all (λ y, P)) ..))
    (in custom lithium at level 200, x binder, y binder, right associativity,
        format "'[' ∀  x  ..  y , ']'  '/' P") : lithium_scope.
Notation "∃ x .. y , P" := (li.exist (λ x, .. (li.exist (λ y, P)) ..))
    (in custom lithium at level 200, x binder, y binder, right associativity,
        format "'[' ∃  x  ..  y , ']'  '/' P") : lithium_scope.

(* Notation "∀ T" := (li.uni T) (in custom lithium at level 0, T constr) : lithium_scope. *)
(* Notation "∃ T" := (li.exi T) (in custom lithium at level 0, T constr) : lithium_scope. *)

Notation "y ; z" := (li.bind0 y z)
  (in custom lithium at level 100, z at level 200,
      format "y ;  '/' z") : lithium_scope.
Notation "x ← y ; z" := (li.bind1 y (λ x : _, z))
  (in custom lithium at level 0, x name, y at level 99, z at level 200,
      format "x  ←  y ;  '/' z") : lithium_scope.
Notation "' x ← y ; z" := (li.bind1 y (λ x : _, z))
  (in custom lithium at level 0, x strict pattern, y at level 99, z at level 200,
      format "' x  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 ← y ; z" := (li.bind2 y (λ x1 x2 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 200, x1 name, x2 name,
      format "x1 ,  x2  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 , x3 ← y ; z" := (li.bind3 y (λ x1 x2 x3 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 200, x1 name, x2 name, x3 name,
      format "x1 ,  x2 ,  x3  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 , x3 , x4 ← y ; z" := (li.bind4 y (λ x1 x2 x3 x4 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 200, x1 name, x2 name, x3 name, x4 name,
      format "x1 ,  x2 ,  x3 ,  x4  ←  y ;  '/' z") : lithium_scope.
Notation "x1 , x2 , x3 , x4 , x5 ← y ; z" := (li.bind5 y (λ x1 x2 x3 x4 x5 : _, z))
  (in custom lithium at level 0, y at level 99, z at level 200, x1 name, x2 name, x3 name, x4 name, x5 name,
      format "x1 ,  x2 ,  x3 ,  x4 ,  x5  ←  y ;  '/' z") : lithium_scope.

Declare Reduction liFromSyntax_eval :=
  cbv [ li.exhale li.inhale li.all li.exist li.done li.false
        li.bind0 li.bind1 li.bind2 li.bind3 li.bind4 li.bind5 ].

Ltac liFromSyntaxTerm c :=
  eval liFromSyntax_eval in c.

Ltac liFromSyntax :=
  match goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
      let Q := liFromSyntaxTerm P in
      change (envs_entails Δ Q)
  end.

Definition liToSyntax_UNFOLD_MARKER {A} (x : A) : A := x.
(* This tactic heurisitically converts the goal to the Lithium syntax.
It is not perfect as it might convert occurences to Lithium syntax
that should stay in Iris syntax, so it should only be used for
debugging and pretty printing.
TODO: Build a proper version using Ltac2, see
https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Controlling.20printing.20of.20patters.20in.20binders/near/363637321
 *)
Ltac liToSyntax :=
  iEval (
    liToSyntax_hook;
    change (bi_sep ?a) with (li.bind0 (li.exhale (liToSyntax_UNFOLD_MARKER a)));
    change (bi_wand ?a) with (li.bind0 (li.inhale (liToSyntax_UNFOLD_MARKER a)));
    change (@bi_forall (iPropI ?Σ) ?A) with (@li.all Σ A);
    change (@bi_exist (iPropI ?Σ) ?A) with (@li.exist Σ A);
    change (@bi_pure (iPropI ?Σ) True) with (@li.done Σ);
    change (@bi_pure (iPropI ?Σ) False) with (@li.false Σ);
    change (find_in_context ?a) with (li.bind1 (find_in_context a));
    change (subsume ?a ?b) with (li.bind0 (subsume (liToSyntax_UNFOLD_MARKER a) (liToSyntax_UNFOLD_MARKER b)));
    change (subsume_list ?A ?ig ?l1 ?l2 ?f) with (li.bind0 (subsume_list A ig l1 l2 f));
    change (tactic_hint ?t) with (li.bind1 (tactic_hint t));
    change (accu ?f) with (li.bind1 (accu f));
    change (destruct_hint ?hint ?info) with (li.bind0 (destruct_hint hint info));
    (* Try to at least unfold some spurious conversions. *)
    repeat (progress change (liToSyntax_UNFOLD_MARKER (li.bind0 (@li.exhale ?Σ ?a) ?b))
        with (a ∗ liToSyntax_UNFOLD_MARKER b)%I);
    change (liToSyntax_UNFOLD_MARKER (@li.done ?Σ)) with (@bi_pure (iPropI Σ) True);
    change (liToSyntax_UNFOLD_MARKER (@li.false ?Σ)) with (@bi_pure (iPropI Σ) False);
    unfold liToSyntax_UNFOLD_MARKER).

(* The following looses the printing of patterns and is extremely slow
when going under many binders (e.g. typed_place). *)
(*
Ltac to_li c :=
  lazymatch c with
  | bi_sep ?P ?G =>
      refine (li.bind0 (li.exhale P) _);
      to_li G
  | bi_wand ?P ?G =>
      refine (li.bind0 (li.inhale P) _);
      to_li G
  | @bi_forall _ ?A (fun x => @?G x) =>
      refine (@li.all _ A (λ x, _));
      let y := eval lazy beta in (G x) in
      to_li y
  | @bi_exist _ ?A (fun x => @?G x) =>
      refine (@li.exist _ A (λ x, _));
      let y := eval lazy beta in (G x) in
      to_li y
  | @bi_exist _ ?A (fun x => @?G x) =>
      refine (@li.exist _ A (λ x, _));
      let y := eval lazy beta in (G x) in
      to_li y
  | True%I => refine (li.done)
  | ?P (fun x => @?G x) =>
      (* idtac x; *)
      refine (li.bind1 P (λ x, _));
      let y := eval lazy beta in (G x) in
      (* idtac y; *)
      to_li y
  | match ?x with | (a, b) => @?G a b end =>
      refine (match x with | (a, b) => _ end);
      let y := eval lazy beta in (G a b) in
      (* idtac y;       *)
      to_li y
  | ?G =>
      refine (G)
  end.

Ltac goal_to_li :=
  match goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
      let x := fresh in
      unshelve evar (x : bi_car PROP); [to_li P|];
      change (envs_entails Δ x); unfold x; clear x
  end.
*)

Module li_test.
Section test.

  Context {Σ : gFunctors}.
  Parameter check_wp : ∀ (e : Z) (T : Z → iProp Σ), iProp Σ.
  Parameter get_tuple : ∀ (T : (Z * Z * Z) → iProp Σ), iProp Σ.

  Local Ltac liToSyntax_hook ::=
    change (check_wp ?x) with (li.bind1 (check_wp x));
    change (get_tuple) with (li.bind1 (get_tuple)).

  Lemma ex1_1 :
    ⊢ get_tuple (λ '(x1, x2, x3), ⌜x1 = 0⌝ ∗ subsume False False True).
  Proof.
    iStartProof.
    (* Important: '(...) syntax should be preserved *)
    liToSyntax.
    liFromSyntax.
  Abort.

  Lemma ex1_1 :
    ⊢ [{ '(x1, x2, x3) ← {get_tuple}; exhale ⌜x1 = 0⌝; done }].
  Proof.
    iStartProof.
    liFromSyntax.
  Abort.

  Lemma ex1_3 :
    ⊢ ∀ n1 n2, (⌜n1 + Z.to_nat n2 > 0⌝ ∗ ⌜n2 = 1⌝) -∗
     check_wp (n1 + 1) (λ v,
       ∃ n' : nat, (⌜v = n'⌝ ∗ ⌜n' > 0⌝) ∗
       get_tuple (λ '(x1, x2, x3), ⌜x1 = 0⌝ ∗ True )).
  Proof.
    iStartProof.
    liToSyntax.
    liFromSyntax.
  Abort.
End test.
End li_test.
