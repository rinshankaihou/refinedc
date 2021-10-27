From refinedc.typing Require Import axioms.

From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Record global_type `{!typeG Σ} := GT {
  gt_A : Type;
  gt_type : gt_A → type;
}.
Arguments GT {_ _} _ _.

Class globalG `{!typeG Σ} := {
  global_locs : gmap string loc;
  global_initialized_types : gmap string global_type;
}.
Arguments globalG _ {_}.

Section globals.
  Context `{!typeG Σ} `{!globalG Σ}.
  Import EqNotations.

  Definition global_with_type (name : string) (β : own_state) (ty : type) : iProp Σ :=
    (∃ l, ⌜global_locs !! name = Some l⌝ ∗ l ◁ₗ{β} ty)%I.

  (* A version of initialized that does not depend on globalG. This is
  a work-around to allow the type of one global to refer to another as
  long as there are no cycles (see t_adequacy). The proper solution
  would be to use higher-order ghost state instead of globalG. *)
  Definition initialized_raw {A} (name : string) (x : A) (l' : option loc) (ty' : option global_type)  : iProp Σ :=
    (∃ l ty, ⌜l' = Some l⌝ ∗ ⌜ty' = Some ty⌝ ∗
          ∃ Heq : A = ty.(gt_A), l ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x))%I.

  Definition initialized {A} (name : string) (x : A) : iProp Σ :=
    initialized_raw name x (global_locs !! name) (global_initialized_types !! name).

  Global Instance initialized_persistent A name (x : A) : Persistent (initialized name x).
  Proof. apply _. Qed.

  Global Instance initialized_intro_persistent A name (x : A) : IntroPersistent (initialized name x) (initialized name x).
  Proof. constructor. iIntros "#$". Qed.

  Lemma simplify_global_with_type_hyp name β ty T:
    (∀ l, ⌜global_locs !! name = Some l⌝ -∗ l ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp (global_with_type name β ty) T.
  Proof. iIntros "HT". iDestruct 1 as (l' ?) "Hl". by iApply "HT". Qed.
  Global Instance simplify_global_with_type_hyp_inst name β ty:
    SimplifyHyp (global_with_type name β ty) (Some 0%N) :=
    λ T, i2p (simplify_global_with_type_hyp name β ty T).

  Lemma simplify_global_with_type_goal name β ty l T `{!TCFastDone (global_locs !! name = Some l)} :
    T (l ◁ₗ{β} ty) -∗
    simplify_goal (global_with_type name β ty) T.
  Proof. unfold TCFastDone in *. iIntros "HT". iExists _. iFrame. iIntros "?". iExists _. by iFrame. Qed.
  Global Instance simplify_global_with_type_goal_inst name β ty l `{!TCFastDone (global_locs !! name = Some l)}:
    SimplifyGoal (global_with_type name β ty) (Some 0%N) :=
    λ T, i2p (simplify_global_with_type_goal name β ty l T).

  Lemma simplify_initialized_hyp A (x : A) name ty l T `{!TCFastDone (global_locs !! name = Some l)}  `{!TCFastDone (global_initialized_types !! name = Some ty)}:
    (∃ (Heq : A = ty.(gt_A)), l ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x) -∗ T) -∗
    simplify_hyp (initialized name x) T.
  Proof.
    unfold TCFastDone in *. iDestruct 1 as (?) "HT". iDestruct 1 as (l' ??? Heq2) "Hl". simplify_eq. iApply "HT" => /=.
    (** HERE WE USE AXIOM K! *)
    by rewrite (UIP_refl _ _ Heq2).
  Qed.
  Global Instance simplify_initialized_hyp_inst A x name ty l `{!TCFastDone (global_locs !! name = Some l)} `{!TCFastDone (global_initialized_types !! name = Some ty)}:
    SimplifyHyp (initialized name x) (Some 0%N) :=
    λ T, i2p (simplify_initialized_hyp A x name ty l T).

  Lemma initialized_intro A ty name l (x : A) :
    global_locs !! name = Some l →
    global_initialized_types !! name = Some ty →
    (∃ (Heq : A = ty.(gt_A)), l ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x)) -∗
    initialized name x.
  Proof. iIntros (??) "Hl". iExists _, _. by iFrame. Qed.

  Lemma simplify_initialized_goal A (x : A) name l ty T `{!TCFastDone (global_locs !! name = Some l)} `{!TCFastDone (global_initialized_types !! name = Some ty)} :
    T ((∃ (Heq : A = ty.(gt_A)), l ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x))) -∗
    simplify_goal (initialized name x) T.
  Proof. unfold TCFastDone in *. iIntros "HT". iExists _. iFrame. by iApply initialized_intro. Qed.
  Global Instance simplify_initialized_goal_inst A (x : A) name ty l `{!TCFastDone (global_locs !! name = Some l)}  `{!TCFastDone (global_initialized_types !! name = Some ty)}:
    SimplifyGoal (initialized name x) (Some 0%N) :=
    λ T, i2p (simplify_initialized_goal A x name l ty T).


  (** Subsumption *)
  Definition FindInitialized (name : string) (A : Type) :=
  {| fic_A := A; fic_Prop x:= (initialized name x); |}.
  Global Instance related_to_initialized name A (x : A) : RelatedTo (initialized name x) :=
    {| rt_fic := FindInitialized name A |}.

  Lemma find_in_context_initialized name A T:
    (∃ x, initialized name x ∗ T x) -∗
    find_in_context (FindInitialized name A) T.
  Proof. iDestruct 1 as (x) "[Hinit HT]". iExists _. iFrame. Qed.
  Global Instance find_in_context_initialized_inst name A :
    FindInContext (FindInitialized name A) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_initialized name A T).

  Lemma subsume_initialized name A (x1 x2 : A) T:
    ⌜x1 = x2⌝ ∗ T -∗
    subsume (initialized name x1) (initialized name x2) T.
  Proof. iIntros "[-> $] $". Qed.
  Global Instance subsume_initialized_inst name A (x1 x2 : A):
    Subsume (initialized name x1) (initialized name x2) :=
    λ T, i2p (subsume_initialized name A x1 x2 T).

End globals.

Typeclasses Opaque initialized global_with_type.
