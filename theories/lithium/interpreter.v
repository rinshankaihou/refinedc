From iris.proofmode Require Import coq_tactics reduction.
From refinedc.lithium Require Import base infrastructure classes simpl_classes tactics_extend.

(** * Definitions of markers for controling the state *)
Definition IPM_STATE {PROP : bi} (n : positive) := envs PROP.
Arguments IPM_STATE : simpl never.
Notation "'HIDDEN'" := (Envs _ _ _) (only printing).

Definition LET_ID {A} (x : A) : A := x.
Arguments LET_ID : simpl never.
Notation "'HIDDEN'" := (LET_ID _) (only printing).

Definition EVAR_ID {A} (x : A) : A := x.
Arguments EVAR_ID : simpl never.

(** * Lemmas used by tactics *)
Section coq_tactics.
  Context {Σ : gFunctors}.

  Lemma tac_fast_apply {Δ} {P1 P2 : iProp Σ} :
    (P1 -∗ P2) → envs_entails Δ P1 → envs_entails Δ P2.
  Proof. by rewrite envs_entails_eq => -> HP. Qed.

  Lemma tac_fast_apply_below_sep {Δ} {P1 P2 T : iProp Σ} :
    (P1 -∗ P2) → envs_entails Δ (P1 ∗ T) → envs_entails Δ (P2 ∗ T).
  Proof. by rewrite envs_entails_eq => -> HP. Qed.

  Lemma tac_protected_eq_app {A} (f : A → Prop) a :
    f a → f (protected a).
  Proof. by rewrite protected_eq. Qed.

  Lemma tac_protected_eq_app_rev {A} (f : A → Prop) a :
    f (protected a) → f a.
  Proof. by rewrite protected_eq. Qed.

  Lemma tac_exist_prod A B (P : _ → Prop):
    (∃ x1 x2, P (x1, x2)) → @ex (A * B) P.
  Proof. move => [?[??]]. eauto. Qed.

  Lemma tac_exist_sigT A f (P : _ → Prop):
    (∃ (a : A) (x : f a), P (existT a x)) → @ex (sigT f) P.
  Proof. move => [?[??]]. eauto. Qed.

  Lemma tac_find_hyp_equal key (Q P P' R : iProp Σ) Δ `{!FindHypEqual key Q P P'}:
    envs_entails Δ (P' ∗ R) →
    envs_entails Δ (P ∗ R).
  Proof. by revert select (FindHypEqual _ _ _ _) => ->. Qed.

  Lemma tac_find_hyp Δ i p R (P : iProp Σ) :
    envs_lookup i Δ = Some (p, P) →
    envs_entails (envs_delete false i p Δ) R → envs_entails Δ (P ∗ R).
  Proof.
    rewrite envs_entails_eq. intros ? HQ.
    rewrite (envs_lookup_sound' _ false) // bi.intuitionistically_if_elim.
      by apply bi.sep_mono_r.
  Qed.

  Lemma tac_do_exist A Δ (P : A → iProp Σ) :
    (∃ x, envs_entails Δ (P x)) → envs_entails Δ (∃ x : A, P x).
  Proof.
    rewrite envs_entails_eq. intros [x HP]. by rewrite -(bi.exist_intro x).
  Qed.

  Lemma tac_do_forall A Δ (P : A → iProp Σ) :
    (∀ x, envs_entails Δ (P x)) → envs_entails Δ (∀ x : A, P x).
  Proof.
    rewrite envs_entails_eq. intros HP. by apply bi.forall_intro.
  Qed.
  Lemma tac_do_exist_wand A Δ (P : A → iProp Σ) Q :
    (∀ x, envs_entails Δ (P x -∗ Q)) → envs_entails Δ ((∃ x : A, P x) -∗ Q).
  Proof.
    rewrite envs_entails_eq. iIntros (HP) "Henv". iDestruct 1 as (x) "HP".
    by iApply (HP with "Henv HP").
  Qed.

  Lemma tac_do_intro_pure Δ (P : Prop) (Q : iProp Σ) :
    (P → envs_entails Δ Q) → envs_entails Δ (⌜P⌝ -∗ Q).
  Proof.
    rewrite envs_entails_eq => HP. iIntros "HΔ %".  by iApply HP.
  Qed.

  Lemma tac_do_intro_pure_and Δ (P : Prop) (Q : iProp Σ) :
    (P ∧ (envs_entails Δ Q)) → envs_entails Δ (⌜P⌝ ∗ Q).
  Proof.
    rewrite envs_entails_eq => [[HP HΔ]].
    iIntros "HΔ".  iSplit => //. by iApply HΔ.
  Qed.

  Lemma tac_do_intro_intuit_sep Δ (P Q : iProp Σ) :
    envs_entails (envs_clear_spatial Δ) (P ∗ True) → envs_entails Δ Q → envs_entails Δ (□ P ∗ Q).
  Proof.
    rewrite envs_entails_eq => HP HQ. iIntros "Henv".
    iSplit.
    - iDestruct (envs_clear_spatial_sound with "Henv") as "[#Henv _]".
      iModIntro. iDestruct (HP with "Henv") as "[$ _]".
    - by iApply HQ.
  Qed.

  (* TODO: have a generic super intros which does simplification along
  the awy in an efficient manner and which subsumes SimplifyHypPlace, SimplifyHypVal and SimplImpl*)
  Lemma tac_do_intro i (P : iProp Σ) T Δ o {SH:SimplifyHyp P o} :
    match o, envs_app false (Esnoc Enil i P) Δ with
    | Some 0%N, _ => envs_entails Δ (SH T).(i2p_P)
    | _, None => False
    | _, Some Δ' => envs_entails Δ' T
    end →
    envs_entails Δ (P -∗ T).
  Proof.
    rewrite envs_entails_eq => HP. iIntros "Henv Hl".
    destruct o as [[|?] |]. {
      iDestruct (HP with "Henv") as "HP".
      iDestruct (i2p_proof with "HP Hl") as "$".
    }
    all: case_match => //.
    all: rewrite envs_app_sound //=; simpl.
    all: iDestruct ("Henv" with "[$]") as "Henv".
    all: by iDestruct (HP with "Henv") as "$".
  Qed.

  Lemma tac_do_intro_intuit i (P P' : iProp Σ) T Δ o `{!IntroPersistent P P'} {SH:SimplifyHyp P o} :
    match o, envs_app true (Esnoc Enil i P') Δ with
    | Some 0%N, _ => envs_entails Δ (SH T).(i2p_P)
    | _, None => False
    | _, Some Δ' => envs_entails Δ' T
    end →
    envs_entails Δ (P -∗ T).
  Proof.
    revert select (IntroPersistent _ _) => Hpers.
    rewrite envs_entails_eq => HP. iIntros "Henv HP".
    destruct o as [[|?] |]. {
      iDestruct (HP with "Henv") as "HSH".
      iDestruct (i2p_proof with "HSH HP") as "$".
    }
    all: case_match => //.
    all: iDestruct (@ip_persistent _ _ _ Hpers with "HP") as "#HP'".
    all: rewrite envs_app_sound //=; simpl.
    all: iDestruct ("Henv" with "[$]") as "Henv".
    all: by iDestruct (HP with "Henv") as "$".
  Qed.

  Lemma tac_true Δ :
    envs_entails Δ (True%I : iProp Σ).
  Proof. rewrite envs_entails_eq. by iIntros "_". Qed.

  Lemma tac_sep_true Δ (P : iProp Σ) :
    envs_entails Δ P → envs_entails Δ (True ∗ P).
  Proof. apply tac_fast_apply. by apply bi.True_sep_2. Qed.

  Lemma tac_sep_emp Δ (P : iProp Σ) :
    envs_entails Δ P → envs_entails Δ (emp ∗ P).
  Proof. apply tac_fast_apply. by apply bi.emp_sep_1. Qed.

  Lemma tac_wand_emp Δ (P : iProp Σ) :
    envs_entails Δ P → envs_entails Δ (emp -∗ P).
  Proof. apply tac_fast_apply. by iIntros "$". Qed.

  Lemma tac_sep_sep_assoc Δ (P Q R : iProp Σ) :
    envs_entails Δ (P ∗ Q ∗ R) → envs_entails Δ ((P ∗ Q) ∗ R).
  Proof. apply tac_fast_apply. iIntros "($&$&$)". Qed.

  Lemma tac_wand_sep_assoc Δ (P Q R : iProp Σ) :
    envs_entails Δ (P -∗ Q -∗ R) → envs_entails Δ ((P ∗ Q) -∗ R).
  Proof. by rewrite bi.wand_curry. Qed.

  Lemma tac_sep_exist_assoc {A} Δ (Φ : A → iProp Σ) (Q : iProp Σ):
    envs_entails Δ (∃ a : A, Φ a ∗ Q) → envs_entails Δ ((∃ a : A, Φ a) ∗ Q).
  Proof. by rewrite bi.sep_exist_r. Qed.

  Lemma tac_do_simplify_goal (n : N) (P : iProp Σ) T {SG : SimplifyGoal P (Some n)} :
    (SG (λ P, P ∗ T)%I).(i2p_P) -∗ P ∗ T.
  Proof. iIntros "HP". iDestruct (i2p_proof with "HP") as (?) "(H&?&$)". by iApply "H". Qed.

  Lemma tac_intro_subsume_related P T {Hrel : RelatedTo P}:
    find_in_context Hrel.(rt_fic) (λ x, subsume (Σ:=Σ) (Hrel.(rt_fic).(fic_Prop) x) P T) -∗ P ∗ T.
  Proof. iDestruct 1 as (x) "[HP HT]". by iApply "HT". Qed.

  Lemma tac_remove_inuit (P T : iProp Σ) `{!Persistent P} :
    P ∗ T -∗ □ P ∗ T.
  Proof. by iIntros "[#? $]". Qed.

  Lemma tac_do_accu Δ (f : iProp Σ → iProp Σ):
    envs_entails (envs_clear_spatial Δ) (f (env_to_prop (env_spatial Δ))) →
    envs_entails Δ (accu f).
  Proof.
    rewrite envs_entails_eq => Henv. iIntros "Henv".
    iDestruct (envs_clear_spatial_sound with "Henv") as "[#Henv Hs]". iExists (env_to_prop (env_spatial Δ)).
    rewrite -env_to_prop_sound. iFrame. iModIntro. by iApply (Henv with "Henv").
  Qed.

  Lemma tac_do_split Δ (P1 P2 : iProp Σ):
    envs_entails Δ P1 → envs_entails Δ P2 →
    envs_entails Δ (P1 ∧ P2).
  Proof. rewrite envs_entails_eq => HP1 HP2. by apply bi.and_intro. Qed.

  Lemma tac_split_big_sepM {K A} `{!EqDecision K} `{!Countable K} (m : gmap K A) i x Φ (P : iProp Σ):
    m !! i = None →
    (Φ i x -∗ ([∗ map] k ↦x∈m, Φ k x) -∗ P) -∗
    ([∗ map] k ↦x∈<[i := x]>m, Φ k x) -∗ P.
  Proof.
    move => Hin. rewrite big_sepM_insert //.
    iIntros "HP [? Hm]". by iApply ("HP" with "[$]").
  Qed.

  Lemma tac_big_andM_insert {A B} `{Countable A} (m : gmap A B) i n (Φ : _ → _→ iProp Σ) :
    ⌜m !! i = None⌝ ∗ (Φ i n ∧ [∧ map] k↦v∈m, Φ k v) -∗
    [∧ map] k↦v∈<[i:=n]>m, Φ k v.
  Proof. iIntros "[% HT]". by rewrite big_andM_insert. Qed.

  Lemma tac_big_andM_empty {A B} `{Countable A} (Φ : _ → _→ iProp Σ) :
    True -∗ [∧ map] k↦v∈(∅ : gmap A B), Φ k v.
  Proof. iIntros "_". by rewrite big_andM_empty. Qed.

End coq_tactics.

(** * Optimization: Introduce let-bindings for environment *)
(** Extension point for custom reduction *)
Ltac li_pm_reduce_tac H := H.
Ltac li_pm_reduce_val v :=
  let v := li_pm_reduce_tac v in
  let v := reduction.pm_eval v in v.
Ltac li_pm_reduce :=
  match goal with
  | H : IPM_STATE _ |- _ =>
         match goal with |- ?u =>
                         let u := eval cbv [H] in u in
                         let u := li_pm_reduce_val u in change u
         end
  | |- ?u =>
    let u := li_pm_reduce_val u in
    change u
  end.
Ltac li_pm_reflexivity := li_pm_reduce; exact eq_refl.

Local Tactic Notation "liChangeState" hyp(H) constr(Δ) :=
  match Δ with
  | @Envs ?PROP _ _ ?n =>
    let H' := fresh "IPM_JANNO" in
    pose (H' := Δ);
    change (envs PROP) with (@IPM_STATE PROP n) in H';
    clear H;
    rename H' into H
  end.

Ltac liEnforceInvariant :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
    let with_H tac :=
    match goal with
    | [ H : IPM_STATE _ |- _] =>
      lazymatch Δ with H => tac H | _ => unify Δ (H); tac H end
    | [ H : IPM_STATE _ |- _] =>
      liChangeState H Δ; tac H
    | _ =>
      match Δ with
      | Envs _ _ ?c =>
        let H := fresh "IPM_JANNO" in
        pose (H := Δ);
        change (envs PROP) with (@IPM_STATE PROP c) in H;
        hnf in (value of H);
        tac H
  end
  end in
    with_H ltac:(fun H =>
                   change_no_check (envs_entails H P)
                )
  end.

Ltac liFresh :=
  lazymatch goal with
  | [ H : IPM_STATE ?n |- _ ] =>
  let do_incr :=
    lazymatch goal with
    | H := @Envs ?PROP ?p1 ?p2 ?c |- envs_entails ?H' ?Q =>
      match H' with | H =>
      let c' := eval vm_compute in (Pos.succ c) in
      let H2 := fresh "IPM_INTERNAL" in
      pose (H2 := @Envs PROP p1 p2 c');
      change (envs PROP) with (@IPM_STATE PROP c') in H2;
      change_no_check (@envs_entails PROP H2 Q);
      clear H; rename H2 into H
      end
  end in
    constr:(IAnon n)
  end.

Ltac liUnfoldLetGoal :=
  match goal with
  | |- envs_entails _ ?P =>
    let rec go P tac :=
        match P with
        | ?Q ?R => go Q tac
        | _ => is_var P; tac P
        end in
    go P ltac:(fun P => unfold LET_ID in P; unfold P; try clear P)
  end.

Ltac liUnfoldLetsInContext :=
  repeat match goal with
  | H := LET_ID _ |- _ => unfold LET_ID in H; unfold H; clear H
  | H : IPM_STATE _ |- _  => unfold H; clear H
  end.

(** * Management of evars *)
Ltac liUnfoldAllEvars :=
  repeat rewrite protected_eq;
  repeat match goal with
         | He := EVAR_ID _ |- _ => unfold He, EVAR_ID; clear He
         end.

Ltac create_protected_evar A :=
  (* necessary, otherwise pattern might not find all occurences later, see also instantiate protected *)
  let A := eval cbn in A in
  let Hevar := fresh "Hevar" in
  (* see https://stackoverflow.com/a/46178884*)
  let c :=
      match goal with
      | _ =>
        let x := fresh "x" in
        unshelve evar (x : A); [ liUnfoldAllEvars; liUnfoldLetsInContext; shelve |];
        pose (Hevar := EVAR_ID x : A); unfold x in Hevar; clear x
      end in
  Hevar.

Ltac unfold_instantiated_evar_hook H := idtac.

Ltac unfold_instantiated_evar H :=
  unfold_instantiated_evar_hook H;
  revert H;
  repeat match goal with
        | |- let _ := EVAR_ID ?body in _ =>
          match goal with
          | He := EVAR_ID ?var |- _ => is_evar var;
          lazymatch body with
          | context [ var ] => pattern var;
          lazymatch goal with
          | |- ?G ?E =>
            change (G He);
            simple refine (tac_protected_eq_app_rev _ _ _);
            cbv beta
          end
          end
          end
        end;
  (* This is copied from the end of instantiate_protected *)
  let tmp := fresh "tmp" in
  intros tmp;
  pattern (protected tmp);
  simple refine (tac_protected_eq_app _ _ _);
  unfold tmp, EVAR_ID; clear tmp.

(*
  H should be (protected Hevar) where Hevar is the letbinding of an evar
  tac_with should be something like
  ltac:(fun H => instantiate (1:= (protected (EVAR_ID _) + protected (EVAR_ID _))%nat) in (Value of H)
  it should use instantiate (1:= ...) in (Value of H) to instantiate the first evar in the supplied parameter which will be Hevar
  It can use _ to create new evars, but they should be surrounded by [protected (EVAR_ID _)] such that instantiate_protected can find them and create the right let bindings afterwards.
*)
Ltac instantiate_protected H' tac_with :=
  lazymatch H' with
  | protected ?H =>
    unfold EVAR_ID in H;
    (* we have to be vary careful how we instantiate the evar, as it
    may not rely on things introduced later (even let bindings),
    otherwise unification fails *)
    tac_with H;
    revert H;
    repeat lazymatch goal with
    | |- let _ := ?body in _  =>
      lazymatch body with
      | context [EVAR_ID ?x] =>
        let Hevar := fresh "Hevar" in
        set (Hevar := (EVAR_ID x));
        (* necessary, otherwise pattern might not find all occurences later, see also create_protected_evar *)
        cbn in (type of Hevar)
      end
    end;
    (* This is copied from the end of unfold_instantiated_evar *)
    let tmp := fresh "tmp" in
    intros tmp;
    pattern (protected tmp);
    simple refine (tac_protected_eq_app _ _ _);
    unfold tmp, EVAR_ID; clear tmp
  end.
Tactic Notation "liInst" hyp(H) open_constr(c) :=
  instantiate_protected (protected H) ltac:(fun H => instantiate (1:=c) in (Value of H)).

Ltac unfold_instantiated_evars :=
  repeat match goal with
         | H := EVAR_ID ?x |- _ => assert_fails (is_evar x); unfold_instantiated_evar H
         end.

Create HintDb solve_protected_eq_db discriminated.
Global Hint Constants Opaque : solve_protected_eq_db.

Ltac solve_protected_eq_unfold_tac := idtac.
Ltac solve_protected_eq :=
  (* intros because it is less aggressive than move => * *)
  intros;
  solve_protected_eq_unfold_tac;
  repeat rewrite protected_eq;
  liUnfoldAllEvars;
  lazymatch goal with |- ?a = ?b => unify a b with solve_protected_eq_db end;
  exact: eq_refl.

Ltac liEnforceInvariantAndUnfoldInstantiatedEvars :=
  unfold_instantiated_evars; try liEnforceInvariant.

(** * Checking if the context contains ownership of a certain assertion

  Note that this implementation requires that liEnforceInvariant has been called
  previously when there was a envs_entails goal.
 *)
Ltac liCheckOwnInContext P :=
  let rec go Hs :=
      lazymatch Hs with
      | Esnoc ?Hs2 ?id ?Q =>
        first [ unify Q P with typeclass_instances | go Hs2 ]
      end in
  match goal with
  | H := Envs ?Δi ?Δs _ |- _ =>
      lazymatch (type of H) with | IPM_STATE _ => idtac end;
      first [ go Δs | go Δi ]
  end.
Global Hint Extern 1 (CheckOwnInContext ?P) => (liCheckOwnInContext P; constructor; exact: I) : typeclass_instances.

(** * Main lithium tactics *)
Ltac convert_to_i2p_tac P := fail "No convert_to_i2p_tac provided!".
Ltac convert_to_i2p P cont :=
  lazymatch P with
  | subsume ?P1 ?P2 ?T => cont uconstr:(((_ : Subsume _ _) _).(i2p_proof))
  | subsume_list ?A ?ig ?l1 ?l2 ?f ?T => cont uconstr:(((_ : SubsumeList _ _ _ _ _) _).(i2p_proof))
  | _ => let converted := convert_to_i2p_tac P in cont converted
  end.
Ltac extensible_judgment_hook := idtac.
Ltac liExtensibleJudgement :=
  lazymatch goal with
  | |- envs_entails _ ?P =>
    convert_to_i2p P ltac:(fun converted =>
    simple notypeclasses refine (tac_fast_apply converted _); [solve [refine _] |]; extensible_judgment_hook
  )end.

Ltac liSimpl :=
  simpl.

Ltac liShow := liUnfoldLetsInContext.

Ltac liFindHyp key :=
  let rec go P Hs :=
      lazymatch Hs with
      | Esnoc ?Hs2 ?id ?Q =>
        first [
            lazymatch key with
            | FICSyntactic =>
           (* we first try to unify using the opaquenes hints of
              typeclass_instances. Directly doing exact: eq_refl
              sometimes takes 30 seconds to fail (e.g. when trying
              to unify GetMemberLoc for the same struct but with
              different names. ) TODO: investigate if constr_eq
              could help even more
              https://coq.inria.fr/distrib/current/refman/proof-engine/tactics.html#coq:tacn.constr-eq*)
              unify Q P with typeclass_instances
            | _ =>
              notypeclasses refine (tac_find_hyp_equal key Q _ _ _ _ _); [solve [refine _] | ];
              lazymatch goal with
              | |- envs_entails _ (?P' ∗ _) =>
                unify Q P' with typeclass_instances
              end
            end;
            notypeclasses refine (tac_find_hyp _ id _ _ _ _ _); [li_pm_reflexivity | li_pm_reduce]
          | go P Hs2 ]
      end in
  lazymatch goal with
  | |- envs_entails _ (?P ∗ _) =>
    (* we don't want to try to unify if the goal contains protected
    evars as this can take very long to fail *)
    lazymatch P with
    | context [protected _] => fail "cannot find hyp if it contains protected"
    | _ => idtac
    end;
    let P := li_pm_reduce_val P in
    let run_go P Hs Hi := first [ go P Hs | go P Hi] in
    lazymatch goal with
    | |- envs_entails (Envs ?Hi ?Hs _) _ => run_go P Hs Hi
    | H := (Envs ?Hi ?Hs _) |- _ => run_go P Hs Hi
    end
  end.

Ltac liFindHypOrTrue key :=
  first [
      notypeclasses refine (tac_sep_true _ _ _)
    | progress liFindHyp key
  ].

Ltac custom_exist_tac A protect := fail "No custom_exist_tac provided.".
Ltac liExist protect :=
  lazymatch goal with
  | |- envs_entails _ (bi_exist _) => notypeclasses refine (tac_do_exist _ _ _ _)
  | _ => idtac
  end;
  lazymatch goal with
  | |- @ex ?A _ =>
    first [
        custom_exist_tac A protect
      | lazymatch A with
        | TCForall2 _ _ _ => eexists _
        (* | Type => eexists _ *)
        | @eq ?B ?x _ => exists (@eq_refl B x)
        | prod _ _ => apply: tac_exist_prod
        | sigT _ => apply: tac_exist_sigT
        | unit => exists tt
        | ?A =>
          lazymatch protect with
          | true => let Hevar := create_protected_evar A in exists (protected Hevar)
          | false => eexists _
          end
        end ]
  | _ => fail "do_exist: unknown goal"
  end.


Ltac liFindInContext :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context ?fic ?T) =>
    let rec go n :=
        let inst := eval cbv beta in (_ : FindInContext fic n _) in
        first [
          lazymatch (type of inst) with
          | FindInContext _ _ ?key =>
          simple notypeclasses refine (tac_fast_apply (inst _).(i2p_proof) _); simpl;
          repeat liExist false; liFindHypOrTrue key
          end
         | go constr:(S n)
        ]
    in
    go constr:(0%nat)
  end.

Ltac liTrue :=
  lazymatch goal with
  | |- envs_entails _ True => notypeclasses refine (tac_true _)
  end.

Ltac liFalse :=
  lazymatch goal with
  | |- envs_entails _ False => exfalso; shelve
  | |- False => shelve
  end.


Ltac liImpl :=
  lazymatch goal with
  (* relying on the fact that unification variables cannot contain
  dependent variables to distinguish between dependent and non dependent forall *)
  | |- ?P -> ?Q =>
    lazymatch type of P with
    | Prop => first [
              progress normalize_goal_impl; simpl
            |
            (*
              one could also try getting rid of the equality in the goal with something like the
              following, but it does not seem to be much faster:
              let inst := eval unfold li_this_is_a_dummy_definition in (_ : SimplImplUnsafe _ P _) in
              lazymatch (type of inst) with
              | SimplImplUnsafe false _ _ =>
             *)
            apply: apply_simpl_impl; simpl;
              match goal with
              | |- true = true -> _ => move => _
              | |- false = false -> ?P → _ => move => _;
                match P with
                | ∃ _, _ => fail 1 "handled by do_forall"
                | _ = _ => let Hi := fresh "Hi" in move => Hi; injection Hi; clear Hi
                | _ => check_hyp_not_exists P; intros ?; subst
                | _ => move => _
                end
              end
            ]
    (* just some unused variable, forget it *)
    | _ => move => _
    end
  end.

Ltac liForall :=
  let do_intro name :=
    repeat lazymatch goal with
    (* relying on the fact that unification variables cannot contain
       dependent variables to distinguish between dependent and non dependent forall *)
    | |- ?P -> ?Q => fail "implication, not forall"
    | |- forall _ : ?P, _ =>
      (* When changing this, also change [prepare_initial_coq_context] in automation.v *)
      lazymatch P with
      | (prod _ _) => case
      | unit => case
      | _ => let H := fresh name in intro H
      end
    end
  in
  lazymatch goal with
  | |- envs_entails _ (bi_forall (λ name, _)) => notypeclasses refine (tac_do_forall _ _ _ _); do_intro name
  | |- envs_entails _ (bi_wand (bi_exist (λ name, _)) _) =>
    notypeclasses refine (tac_do_exist_wand _ _ _ _ _); do_intro name
  | |- (∃ name, _) → _ => case; do_intro name
  | |- forall name, _ => do_intro name
  | _ => fail "do_forall: unknown goal"
  end.

(* This tactic checks if destructing x would lead to multiple
non-trivial subgoals. The main reason for it is that we don't want to
destruct constructors like true as this would not be useful. *)
Ltac non_trivial_destruct x :=
  first [
      have : (const False x); [ clear; case_eq x; intros => //; (*
      check if there is only one goal remaining *) [ idtac ]; fail 1 "trivial destruct" |]
    | idtac
  ].

Ltac record_destruct_hint hint info := idtac.
Ltac liDestructHint :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (destruct_hint ?hint ?info ?T) =>
    change_no_check (@envs_entails PROP Δ T);
    lazymatch hint with
    | DHintInfo =>
       record_destruct_hint hint info
    | DHintDestruct _ (@bool_decide ?P ?b) =>
      let H := fresh "H" in destruct_decide (@bool_decide_reflect P b) as H; revert H; [
      record_destruct_hint hint (info, true) |
      record_destruct_hint hint (info, false) ]
    | DHintDestruct _ ?x =>
      tryif (non_trivial_destruct x) then
        case_eq x; repeat liForall;
        lazymatch goal with
        | |- _ = ?res → _ =>
          record_destruct_hint hint (info, res)
        end
      else (
          idtac
        )
    | @DHintDecide ?P ?b =>
       let H := fresh "H" in destruct_decide (@decide P b) as H; revert H; [
      record_destruct_hint hint (info, true) |
      record_destruct_hint hint (info, false) ]
    end
  end; repeat (liForall || liImpl); try by [exfalso; can_solve_tac].

Ltac liAccu :=
  lazymatch goal with
  | |- envs_entails _ (accu _) =>
    notypeclasses refine (tac_do_accu _ _ _); li_pm_reduce
  end.

Ltac liSideCond :=
  lazymatch goal with
  | |- ?P ∧ _ =>
    lazymatch P with
    | shelve_hint _ => split; [ unfold shelve_hint; shelve |]
    | _ => first [ progress normalize_goal_and |
    lazymatch P with
    | context [protected _] => first [
        split; [ solve_protected_eq |]; unfold_instantiated_evars
      | notypeclasses refine (apply_simpl_and _ _ _ _ _); [ solve [refine _] |]; simpl;
        lazymatch goal with
        | |- true = true -> _ => move => _
        | _ => fail "could not simplify goal with evar"
        end
      ]
     (* We use done instead of fast_done here because solving more
     sideconditions here is a bigger performance win than the overhead
     of done. *)
    | _ => split; [ first [ done | shelve ] | ]
    end ] end
  | _ => fail "do_side_cond: unknown goal"
  end.

Ltac liSep :=
  lazymatch goal with
  | |- envs_entails _ (bi_sep ?P _) =>
    assert_fails (has_evar P);
    lazymatch P with
    | bi_sep _ _ => notypeclasses refine (tac_sep_sep_assoc _ _ _ _ _)
    | bi_exist _ => notypeclasses refine (tac_sep_exist_assoc _ _ _ _)
    | bi_emp => notypeclasses refine (tac_sep_emp _ _ _)
    | (⌜_⌝)%I => notypeclasses refine (tac_do_intro_pure_and _ _ _ _)
    (* TODO: Is this really the right thing to do? *)
    | (□ ?P)%I => notypeclasses refine (tac_do_intro_intuit_sep _ _ _ _ _)
    | match ?x with _ => _ end => fail "should not have match in sep"
    | ?P => first [
               convert_to_i2p P ltac:(fun converted =>
               simple notypeclasses refine (tac_fast_apply_below_sep converted _); [solve[refine _] |])
             | progress liFindHyp FICSyntactic
             | simple notypeclasses refine (tac_fast_apply (tac_do_simplify_goal 0%N _ _) _); [solve [refine _] |]
             | simple notypeclasses refine (tac_fast_apply (tac_intro_subsume_related _ _) _); [solve [refine _] |];
               simpl; liFindInContext
             | simple notypeclasses refine (tac_fast_apply (tac_do_simplify_goal _ _ _) _); [| solve [refine _] |]
             | fail "do_sep: unknown sidecondition" P
      ]
    end
  end.

Ltac liWand :=
  let wand_intro :=
      let H := liFresh in
      first [
          simple notypeclasses refine (tac_do_intro_intuit H _ _ _ _ _ _); [shelve | shelve | solve [refine _] | solve [refine _] | li_pm_reduce]
         | simple notypeclasses refine (tac_do_intro H _ _ _ _ _); [shelve | solve [refine _] | li_pm_reduce]
        ] in
  lazymatch goal with
  | |- envs_entails _ (bi_wand ?P _) =>
      lazymatch P with
      | bi_sep _ _ => notypeclasses refine (tac_wand_sep_assoc _ _ _ _ _)
      | bi_exist _ => fail "handled by do_forall"
      | bi_emp => notypeclasses refine (tac_wand_emp _ _ _)
      | bi_pure _ => notypeclasses refine (tac_do_intro_pure _ _ _ _)
      | match ?x with _ => _ end => fail "should not have match in wand "
      | _ => wand_intro
      end
  end.

Ltac liAnd :=
  lazymatch goal with
  | |- envs_entails _ (bi_and ?P _) =>
    notypeclasses refine (tac_do_split _ _ _ _ _)
  | |- envs_entails _ ([∧ map] _↦_∈<[_:=_]>_, _) =>
    notypeclasses refine (tac_fast_apply (tac_big_andM_insert _ _ _ _) _)
  | |- envs_entails _ ([∧ map] _↦_∈∅, _) =>
    notypeclasses refine (tac_fast_apply (tac_big_andM_empty _) _)
  end.

Ltac liStep :=
  first [
      liExtensibleJudgement
    | liSep
    | liAnd
    | liWand
    | liExist true
    | liImpl
    | liForall
    | liSideCond
    | liFindInContext
    | liDestructHint
    | liTrue
    | liFalse
    | liAccu
    | liUnfoldLetGoal
    ].
