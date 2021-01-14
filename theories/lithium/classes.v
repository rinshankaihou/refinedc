(** Main typeclasses of Lithium *)
From refinedc.lithium Require Import base.

(** * [iProp_to_Prop] *)
Record iProp_to_Prop {Σ} (P : iProp Σ) : Type := i2p {
  i2p_P :> iProp Σ;
  i2p_proof : i2p_P -∗ P;
}.
Arguments i2p {_ _ _} _.
Arguments i2p_P {_ _} _.
Arguments i2p_proof {_ _} _.

(** * [find_in_context] *)
(** ** Definition  *)
Record find_in_context_info {Σ} : Type := {
  fic_A : Type;
  fic_Prop : fic_A → iProp Σ;
}.
(* The nat n is necessary to allow different options, they are tried starting from 0. *)
Definition find_in_context {Σ} (fic : find_in_context_info) (T : fic.(fic_A) → iProp Σ) : iProp Σ :=
  (∃ b, fic.(fic_Prop) b ∗ T b).
Class FindInContext {Σ} (fic : find_in_context_info) (n : nat) : Type :=
  find_in_context_proof T: iProp_to_Prop (Σ:=Σ) (find_in_context fic T).

(** ** Instances  *)
Definition FindDirect {Σ A} (P : A → iProp Σ) := {| fic_A := A; fic_Prop := P; |}.
Typeclasses Opaque FindDirect.

Lemma find_in_context_direct {Σ B} P (T : B → iProp Σ):
  (∃ x : B, P x ∗ T x) -∗
   find_in_context (FindDirect P) T.
Proof. done. Qed.
Global Instance find_in_context_direct_inst {Σ B} (P : _ → iProp Σ) :
  FindInContext (FindDirect P) 0%nat :=
  λ T : B → _, i2p (find_in_context_direct P T).


(** * [destruct_hint] *)
Inductive destruct_hint_info :=
| DHintInfo
| DHintDestruct (A : Type) (x : A)
| DHintDecide (P : Prop) `{!Decision P}.
Definition destruct_hint {Σ B} (hint : destruct_hint_info) (info : B) (T : iProp Σ) : iProp Σ := T.
Typeclasses Opaque destruct_hint.
Arguments destruct_hint : simpl never.

(** * [RelatedTo] *)
Class RelatedTo {Σ} (pat : iProp Σ) : Type := {
  rt_fic : find_in_context_info (Σ:=Σ);
}.
Arguments rt_fic {_ _} _.

(** * [IntroPersistent] *)
(** ** Definition *)
Class IntroPersistent {Σ} (P P' : iProp Σ) := {
  ip_persistent : P -∗ □ P'
}.
(** ** Instances *)
Global Instance intro_persistent_intuit Σ (P : iProp Σ) : IntroPersistent (□ P) P.
Proof. constructor. iIntros "$". Qed.

(** * [accu] *)
Definition accu {Σ} (f : iProp Σ → iProp Σ) : iProp Σ :=
  ∃ P, P ∗ □ f P.
Arguments accu : simpl never.
Typeclasses Opaque accu.


(** * Simplification *)
(** ** Definition *)
(* n:
   None: no simplification
   Some 0: simplification which is always safe
   Some n: lower n: should be done before higher n (when compared with simplifyGoal)   *)
Definition simplify_hyp {Σ} (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
  P -∗ T.
Class SimplifyHyp {Σ} (P : iProp Σ) (n : option N) : Type :=
  simplify_hyp_proof T : iProp_to_Prop (simplify_hyp P T).

Definition simplify_goal {Σ} (P : iProp Σ) (T : iProp Σ → iProp Σ) : iProp Σ :=
  (∃ P2, (P2 -∗ P) ∗ T P2).
Class SimplifyGoal {Σ} (P : iProp Σ) (n : option N) : Type :=
  simplify_goal_proof T : iProp_to_Prop (simplify_goal P T).

Hint Mode SimplifyHyp + + - : typeclass_instances.
Hint Mode SimplifyGoal + ! - : typeclass_instances.

(** ** Instances *)
Lemma simplify_hyp_id {Σ} (P : iProp Σ) T:
  T -∗ simplify_hyp P T.
Proof. iIntros "HT Hl". iFrame. Qed.
Global Instance simplify_hyp_id_inst {Σ} (P : iProp Σ):
  SimplifyHyp P None | 100 :=
  λ T, i2p (simplify_hyp_id P T).

Lemma simplify_goal_id {Σ} (P : iProp Σ) T:
  T P -∗ simplify_goal P T.
Proof. iIntros "HT". iExists _. iFrame. by iIntros "?". Qed.
Global Instance simplify_goal_id_inst {Σ} (P : iProp Σ):
  SimplifyGoal P None | 100 :=
  λ T, i2p (simplify_goal_id P T).

(* TODO: Is the following useful? *)
(* Lemma simplify_persistent_pure_goal {Σ} (Φ : Prop) T: *)
(*   T ⌜Φ⌝ -∗ simplify_goal (Σ := Σ) (□ ⌜Φ⌝) T. *)
(* Proof. iIntros "HT". iExists _. iFrame. by iIntros (?). Qed. *)
(* Global Instance simplify_persistent_pure_goal_id {Σ} (Φ : Prop): *)
(*   SimplifyGoal (Σ:=Σ) (□ ⌜Φ⌝) (Some 0%N) := *)
(*   λ T, i2p (simplify_persistent_pure_goal Φ T). *)

(* Lemma simplify_persistent_pure_hyp {Σ} (Φ : Prop) T: *)
(*   (⌜Φ⌝ -∗ T) -∗ simplify_hyp (Σ := Σ) (□ ⌜Φ⌝) T. *)
(* Proof. iIntros "HT" (?). by iApply "HT". Qed. *)
(* Global Instance simplify_persistent_pure_hyp_inst {Σ} (Φ : Prop): *)
(*   SimplifyHyp (Σ:=Σ) (□ ⌜Φ⌝) (Some 0%N) := *)
(*   λ T, i2p (simplify_persistent_pure_hyp Φ T). *)

(* Lemma simplify_persistent_sep_hyp {Σ} (P Q : iProp Σ) T: *)
(*   (□ P -∗ □ Q -∗ T) -∗ simplify_hyp (Σ := Σ) (□ (P ∗ Q)) T. *)
(* Proof. iIntros "HT [HP HQ]". iApply ("HT" with "HP HQ"). Qed. *)
(* Global Instance simplify_persistent_sep_hyp_inst {Σ} (P Q : iProp Σ): *)
(*   SimplifyHyp (Σ:=Σ) (□ (P ∗ Q)) (Some 0%N) := *)
(*   λ T, i2p (simplify_persistent_sep_hyp P Q T). *)

(** * Subsumption *)
(** ** Definition *)
Definition subsume {Σ} (P1 P2 T : iProp Σ) : iProp Σ :=
  P1 -∗ P2 ∗ T.
Class Subsume {Σ} (P1 P2 : iProp Σ) : Type :=
  subsume_proof T : iProp_to_Prop (subsume P1 P2 T).
Definition subsume_list {Σ} A (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) : iProp Σ :=
  ⌜length l1 = length l2⌝ -∗ ([∗ list] i↦x∈l1, f i x) -∗ ([∗ list] i↦x∈l2, f i x) ∗ T.
Class SubsumeList {Σ} A (l1 l2 : list A) (f : nat → A → iProp Σ) :  Type :=
  subsume_list_proof T : iProp_to_Prop (subsume_list A l1 l2 f T).

Hint Mode Subsume + + ! : typeclass_instances.
Hint Mode SubsumeList + + + + ! : typeclass_instances.

(** ** Instances *)
Lemma subsume_id {Σ} (P : iProp Σ) T:
  T -∗ subsume P P T.
Proof. iIntros "$ $". Qed.
Global Instance subsume_id_inst {Σ} (P : iProp Σ) : Subsume P P | 1 := λ T, i2p (subsume_id P T).

Lemma subsume_simplify {Σ} (P1 P2 : iProp Σ) T o1 o2 {SH : SimplifyHyp P1 o1} {SG : SimplifyGoal P2 o2}:
    let GH := (SH (P2 ∗ T)%I).(i2p_P) in
    let GG := (SG (λ P, P1 -∗ P ∗ T)%I).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then GG else GH
     | Some n1, _ => GH
     | _, _ => GG
       end in
    G -∗ subsume P1 P2 T.
Proof.
  iIntros "Hs Hl".
  destruct o1 as [n1|], o2 as [n2|] => //. case_match.
  1,3,4: by iDestruct (i2p_proof with "Hs Hl") as "Hsub".
  all: iDestruct (i2p_proof with "Hs") as (P) "[HP HT]".
  all: iDestruct ("HT" with "Hl") as "[HP' $]".
  all: by iApply "HP".
Qed.
Global Instance subsume_simplify_inst {Σ} (P1 P2 : iProp Σ) o1 o2 `{!SimplifyHyp P1 o1} `{!SimplifyGoal P2 o2} `{!TCOneIsSome o1 o2} :
  Subsume P1 P2 | 1000 :=
  λ T, i2p (subsume_simplify P1 P2 T o1 o2).

Lemma subsume_list_eq {Σ} A (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  ⌜l1 = l2⌝ ∗ T -∗ subsume_list A l1 l2 f T.
Proof. by iIntros "[-> $] _ $". Qed.
Global Instance subsume_list_eq_inst {Σ} A l1 l2 f:
  SubsumeList A l1 l2 f | 1000 :=
  λ T : iProp Σ, i2p (subsume_list_eq A l1 l2 f T).

Lemma subsume_list_trivial_eq {Σ} A (l : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  T -∗ subsume_list A l l f T.
Proof. iIntros "$ _ $". Qed.
Global Instance subsume_list_trivial_eq_inst {Σ} A l f:
  SubsumeList A l l f | 5 :=
  λ T : iProp Σ, i2p (subsume_list_trivial_eq A l f T).

Lemma subsume_list_cons {Σ} A (x1 x2 : A) (l1 l2 : list A) (f : nat → A → iProp Σ) (T : iProp Σ) :
  subsume (f 0%nat x1) (f 0%nat x2) (subsume_list A l1 l2 (λ i, f (S i)) T) -∗
          subsume_list A (x1 :: l1) (x2 :: l2) f T.
Proof.
  iIntros "Hs Hlen". iDestruct "Hlen" as %Hlen. inversion Hlen. rewrite !big_sepL_cons.
  iIntros "[H0 H]". iDestruct ("Hs" with "H0") as "[$ Hs]". by iApply "Hs".
Qed.
Global Instance subsume_list_cons_inst {Σ} A x1 x2 l1 l2 f:
  SubsumeList A (x1 :: l1) (x2 :: l2) f | 40 :=
  λ T : iProp Σ, i2p (subsume_list_cons A x1 x2 l1 l2 f T).
