From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_annot code.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset frac agree.
Set Default Proof Using "Type".

Definition lockN : namespace := nroot.@"lockN".
Definition lock_id := gname.

(** Registering the necessary ghost state. *)
Class lockG Σ := LockG {
   lock_inG :> inG Σ (authR (gset_disjUR string));
   lock_excl_inG :> inG Σ (exclR unitO);
}.
Definition lockΣ : gFunctors :=
  #[GFunctor (constRF (authR (gset_disjUR string)));
    GFunctor (constRF (exclR unitO))].
Instance subG_lockG {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.

  Definition spinlock_token (γ : lock_id) (l : list string) : iProp Σ :=
    ∃ s : gset string, ⌜l ≡ₚ elements s⌝ ∗ own γ (● GSet s).

  Definition spinlock (γ : lock_id) : type :=
    struct struct_spinlock [atomic_bool bool_it True (spinlock_token γ [])].

  Global Program Instance movable_spinlock γ : Movable (spinlock γ) := ltac:(apply: movable_struct).

  Program Definition spinlocked_ex {A} (γ : lock_id) (n : string) (x : A) (ty : A → type) : type := {|
    ty_own β l := (match β return _ with
                  | Own => l ◁ₗ ty x
                  | Shr => ∃ γ', inv lockN ((∃ x', l ◁ₗ ty x' ∗ own γ' (Excl ()))  ∨ own γ (◯ GSet {[ n ]}))
                  end)%I
  |}.
  Next Obligation.
    iIntros (A γ n x ty l E HE) "Hl".
    iMod (own_alloc (Excl ())) as (γ') "Hown" => //.
    iExists _. iApply inv_alloc. iIntros "!#". iLeft. iExists _. by iFrame.
  Qed.

  Global Program Instance movable_spinlocked_ex A γ n x (ty : A → type) `{!Movable (ty x)}: Movable (spinlocked_ex γ n x ty) := {|
    ty_layout := (ty x).(ty_layout);
    ty_own_val v := (v ◁ᵥ (ty x))%I;
  |}.
  Next Obligation. iIntros (A γ n x ty ? v) "Hl". by iApply ty_aligned. Qed.
  Next Obligation. iIntros (A γ n x ty ? v) "Hl". by iApply ty_size_eq. Qed.
  Next Obligation. iIntros (A γ n x ty ? l) "Hl". by iApply ty_deref. Qed.
  Next Obligation. iIntros (A γ n x ty ? l l') "Hl". by iApply ty_ref. Qed.


  Lemma spinlock_subsume γ1 γ2 l T β:
    ⌜γ1 = γ2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} spinlock γ1) (l ◁ₗ{β} spinlock γ2) T.
  Proof. iIntros "[-> $] $". Qed.

  Global Instance spinlock_subsume_inst γ1 γ2 l β:
    Subsume (l ◁ₗ{β} spinlock γ1) (l ◁ₗ{β} spinlock γ2) :=
    λ T, i2p (spinlock_subsume γ1 γ2 l T β).

  Lemma spinlocked_simplify_hyp_place A γ n x (ty : A → type) T l:
    (l ◁ₗ ty x -∗ T)  -∗
    simplify_hyp (l ◁ₗ spinlocked_ex γ n x ty) T.
  Proof. done. Qed.
  Global Instance spinlocked_simplify_hyp_place_inst A γ n x (ty : A → type) l:
    SimplifyHypPlace l Own (spinlocked_ex γ n x ty) (Some 0%N) :=
    λ T, i2p (spinlocked_simplify_hyp_place A γ n x ty T l).

  Lemma spinlocked_simplify_goal_place A γ n x (ty : A → type) T l:
    T (l ◁ₗ ty x) -∗
    simplify_goal (l ◁ₗ spinlocked_ex γ n x ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "$". Qed.

  Global Instance spinlocked_simplify_goal_place_inst A γ n x (ty : A → type) l:
    SimplifyGoalPlace l Own (spinlocked_ex γ n x ty) (Some 0%N) :=
    λ T, i2p (spinlocked_simplify_goal_place A γ n x ty T l).

  Lemma spinlocked_subsume A γ n x1 x2 (ty : A → type) l β T:
    ⌜β = Own → x1 = x2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} spinlocked_ex γ n x1 ty) (l ◁ₗ{β} spinlocked_ex γ n x2 ty) T.
  Proof. iIntros "[% $] Hl". by destruct β; naive_solver. Qed.
  Global Instance spinlocked_subsume_inst A γ n x1 x2 (ty : A → type) l β:
    Subsume (l ◁ₗ{β} spinlocked_ex γ n x1 ty) (l ◁ₗ{β} spinlocked_ex γ n x2 ty) | 10 :=
    λ T, i2p (spinlocked_subsume A γ n x1 x2 ty l β T).

  Definition spinlocked_ex_token {A} (γ : lock_id) (n : string) (l : loc) (β : own_state) (ty : A → type)  : iProp Σ :=
    (∀ E x, ⌜↑lockN ⊆ E⌝ -∗ l ◁ₗ ty x ={E}=∗ l ◁ₗ{β} spinlocked_ex γ n x ty ∗ own γ (◯ GSet {[ n ]}))%I.

  Lemma locked_open A n s l γ (x : A) ty β E:
    n ∉ s → ↑lockN ⊆ E →
    l ◁ₗ{β} spinlocked_ex γ n x ty -∗
      spinlock_token γ s ={E}=∗
      ▷ ∃ x', l ◁ₗ ty x' ∗ spinlock_token γ (n :: s) ∗ spinlocked_ex_token γ n l β ty ∗ ⌜β = Own → x = x'⌝.
  Proof.
    iIntros (Hnotin ?) "Hl Hown".
    iDestruct "Hown" as (st Hperm) "Hown". rewrite ->Hperm in Hnotin.
    iMod (own_update with "Hown") as "[Hown Hs]". { eapply auth_update_alloc.
      apply (gset_disj_alloc_empty_local_update st {[n]}). set_solver. }
    rewrite {1}/ty_own /=.
    iAssert (spinlock_token γ (n :: s)) with "[Hown]" as "$". {
      iExists _. iFrame. iPureIntro. rewrite Hperm elements_union_singleton //. set_solver.
    }
    destruct β. { iIntros "!# !#". iExists _. iFrame. iSplit => //. by iIntros (???) "$". }
    iDestruct "Hl" as (γ') "#Hinv".
    iInv "Hinv" as "[Hl|>Hn]" "Hc". 2: {
      iDestruct (own_valid_2 with "Hs Hn") as %Hown. exfalso. move: Hown.
      rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op. set_solver.
    }
    iMod ("Hc" with "[Hs]") as "_". by iRight.
    iIntros "!# !#". iDestruct "Hl" as (x') "[Hl Hexcl]".
    iExists _. iFrame. iSplitL => //.
    (** locked_token *)
    iIntros (E' x'' ?) "Hl".
    iInv "Hinv" as "[H|>$]" "Hc". 1: {
      have ? : Inhabited A by apply (populate x).
      iDestruct "H" as (?) "[_ >He]".
        by iDestruct (own_valid_2 with "Hexcl He") as %Hown%exclusive_l.
    }
    iMod ("Hc" with "[Hl Hexcl]") as "_". 2: by iExists _.
    iModIntro. iLeft. iExists _. iFrame.
  Qed.

  Lemma locked_close A n s l γ (x : A) ty β E:
    ↑lockN ⊆ E →
    spinlocked_ex_token γ n l β ty -∗ l ◁ₗ ty x -∗ spinlock_token γ (n :: s) ={E}=∗
    spinlock_token γ s ∗ l ◁ₗ{β} spinlocked_ex γ n x ty.
  Proof.
    iIntros (HE) "Hlocked Hl Hlock".
    iMod ("Hlocked" with "[//] Hl") as "[$ Hn]".
    iDestruct "Hlock" as (st Hst) "Htok".
    iExists (st ∖ {[n]}). iSplitR. {
      iPureIntro. move: (Hst). rewrite {1}(union_difference_L {[n]} st).
      rewrite ->elements_union_singleton => ?; last set_solver.
      by apply: Permutation.Permutation_cons_inv.
      set_unfold => ??. subst. apply elem_of_elements. rewrite -Hst. set_solver.
    }
    iCombine "Htok" "Hn" as "Htok".
    iMod (own_update with "Htok") as "$" => //.
    eapply auth_update_dealloc.
      by apply gset_disj_dealloc_local_update.
  Qed.

  Lemma annot_unlock A l T β γ n ty (x : A):
    (find_in_context (FindDirect (spinlock_token γ)) (λ s : list string, ⌜n∉s⌝ ∗ (∀ x',
        spinlock_token γ (n :: s) -∗ spinlocked_ex_token γ n l β ty -∗ ⌜β = Own → x = x'⌝ -∗
                       l ◁ₗ ty x' -∗ T))) -∗
    typed_annot_stmt UnlockA l β (spinlocked_ex γ n x ty) T.
  Proof.
    iDestruct 1 as (s) "(Hs&%&HT)". iIntros "Hlocked".
    iMod (locked_open with "Hlocked Hs") as "Htok" => //.
    iApply step_fupd_intro => //. iModIntro.
    iDestruct "Htok" as (x') "(Hl&Hs&Htok&%)".
    by iApply ("HT" with "Hs Htok [//] Hl").
  Qed.
  Global Instance annot_unlock_inst A l β γ n ty (x : A):
    TypedAnnotStmt UnlockA l β (spinlocked_ex γ n x ty) :=
    λ T, i2p (annot_unlock A l T β γ n ty x).


  Lemma type_annot_lock (l : loc) (ty : mtype) T:
    (∃ β γ, subsume (l ◁ᵥ ty) (l ◁ₗ{β} spinlock γ) (
      find_in_context (FindDirect (spinlock_token γ)) (λ s : list string, foldr (λ t T,
        find_in_context (FindDirect (λ '(existT A (l2, ty)), spinlocked_ex_token (A:=A) γ t l2 β ty)) (λ '(existT A (l2, ty)), ∃ x,
          l2 ◁ₗ ty x ∗ (l2 ◁ₗ{β} spinlocked_ex γ t x ty -∗ T))) (l ◁ₗ{β} spinlock γ -∗ spinlock_token γ [] -∗ T) s))) -∗
    typed_annot_expr 1%nat LockA l ty T.
  Proof.
    iDestruct 1 as (β γ) "Hsub". iIntros "Hl".
    iDestruct ("Hsub" with "Hl") as "[Hlock H]".
    iDestruct "H" as (s) "[Htok Hs]".
    iApply step_fupd_intro => //. iModIntro.
    iInduction s as [|t s] "IH" => /=. by iApply ("Hs" with "Hlock Htok").
    iDestruct "Hs" as ([A [l2 ty2]]) "[Hlt H]".
    iDestruct "H" as (x) "[Hl HT]".
    iMod (locked_close with "Hlt Hl Htok") as "[Htok Hl]" => //.
    iApply ("IH" with "Hlock Htok"). by iApply "HT".
  Qed.
  Global Instance type_annot_lock_inst (l : loc) ty :
    TypedAnnotExpr 1%nat LockA l ty :=
    λ T, i2p (type_annot_lock l ty T).
End type.

(* TODO> DO something stronger, e.g. sealing? *)
Typeclasses Opaque spinlock spinlocked_ex spinlock_token spinlocked_ex_token.
Notation spinlocked γ n ty := (spinlocked_ex γ n tt (λ _, ty)).
Notation spinlocked_token γ n l β ty := (spinlocked_ex_token γ n l β (λ _ : unit, ty)).
