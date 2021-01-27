From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.spinlock Require Import spinlock_annot.
From refinedc.linux.pkvm.spinlock Require Import generated_code.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra Require Import big_op gset gmap frac agree excl_auth.
Set Default Proof Using "Type".

Open Scope Z.

Notation range k n := (seqZ k (n - k)) (only parsing).

Notation LAST_TICKET := (max_int u16 - 1) (only parsing).
Notation NO_TICKET   := (max_int u16) (only parsing).

Definition lockN : namespace := nroot.@"lockN".

Record lock_id := mk_lock_id {
  γ_lock    : gname;
  γ_tickets : gname;
  γ_owner   : gname;
}.

(** Registering the necessary ghost state. *)
Class lockG Σ := LockG {
   lock_inG :> inG Σ (authR (gset_disjUR string));
   lock_excl_inG :> inG Σ (exclR unitO);
   lock_tickets_inG :> inG Σ (gmapR Z (exclR unitO));
   lock_owner_inG :> inG Σ (excl_authR ZO);
}.
Definition lockΣ : gFunctors :=
  #[GFunctor (constRF (authR (gset_disjUR string)));
    GFunctor (constRF (exclR unitO));
    GFunctor (constRF (gmapR Z (exclR unitO)));
    GFunctor (constRF (excl_authR ZO))].
Instance subG_lockG {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.

  Definition owner_auth (γ : gname) (i : Z) : iProp Σ :=
    own γ (●E i).

  Definition owner_frag (γ : gname) (i : Z) : iProp Σ :=
    own γ (◯E i).

  Definition lock_token_token (γ : gname) (l : list string) : iProp Σ :=
    ∃ s : gset string, ⌜l ≡ₚ elements s⌝ ∗ own γ (● GSet s).

  Definition lock_token (id : lock_id) (l : list string) : iProp Σ :=
    ∃ i, lock_token_token id.(γ_lock) l ∗ owner_auth id.(γ_owner) i.

  Theorem lock_token_token_exclusive (γ : gname) (l1 l2 : list string):
    lock_token_token γ l1 -∗ lock_token_token γ l2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (?) "[? H1]".
    iDestruct "H2" as (?) "[? H2]".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %H%auth_auth_op_valid.
    by iPureIntro.
  Qed.

  Definition ticket_aux (γ : gname) (i : Z) : iProp Σ :=
    own γ {[i := Excl ()]} ∗ ⌜i ≠ NO_TICKET⌝.

  Definition ticket (id : lock_id) (i : Z) : iProp Σ :=
    ticket_aux id.(γ_tickets) i.

  Definition ticket_range_def (id : lock_id) (k n : Z) : iProp Σ :=
    [∗ list] i ∈ range k n, ticket id i.

  Definition ticket_range_aux : seal (@ticket_range_def). by eexists. Qed.
  Definition ticket_range := unseal ticket_range_aux.
  Definition ticket_range_eq : @ticket_range = @ticket_range_def :=
    seal_eq ticket_range_aux.

  Global Instance ticket_range_timeless id k n: Timeless (ticket_range id k n).
  Proof. rewrite ticket_range_eq. apply _. Qed.

  Theorem ticket_range_empty (id : lock_id) (n : Z) :
    ⊢ True ∗-∗ ticket_range id n n.
  Proof.
    rewrite ticket_range_eq /ticket_range_def Z.sub_diag /=.
    by iSplit.
  Qed.

  Theorem ticket_range_insert_r (id : lock_id) (k n : Z) :
    0 ≤ k ≤ n →
    ticket_range id k n -∗ ticket id n -∗ ticket_range id k (n + 1).
  Proof.
    iIntros ([??]) "H1 H2". rewrite ticket_range_eq /ticket_range_def.
    assert (n + 1 - k = n - k + 1) as -> by lia.
    rewrite seqZ_app /=; [.. | by lia | by lia].
    assert (k + (n - k) = n) as -> by lia. by iFrame.
  Qed.

  Theorem split_first_ticket (id : lock_id) (k n : Z) :
    0 ≤ k < n →
    ticket_range id k n -∗ ticket id k ∗ ticket_range id (k + 1) n.
  Proof.
    iIntros ([??]) "H". rewrite ticket_range_eq /ticket_range_def.
    assert (n - (k + 1) = n - k - 1) as -> by lia.
    assert (n - k > 0) as Hnk by lia. revert Hnk. generalize (n-k).
    clear. move => n Hn.
    assert (∃ m, n = 1 + m ∧ 0 ≤ m) as [m [-> ?]].
    { exists (n - 1). split; lia. }
    rewrite seqZ_app /=; try by lia. assert (1 + m - 1 = m) as -> by lia.
    by iFrame.
  Qed.

  Theorem ticket_non_duplicable (id : lock_id) (i1 i2 : Z) :
    i1 = i2 →
    ticket id i1 -∗ ticket id i2 -∗ False.
  Proof.
    iIntros (->) "[H1 _] [H2 _]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %H. iPureIntro.
    apply singleton_valid in H. by eapply exclusive_r.
  Qed.

  Theorem ticket_not_NO_TICKET (id : lock_id) (i : Z) :
    ticket id i -∗ ⌜i ≠ NO_TICKET⌝.
  Proof.
    iIntros "[_ $]".
  Qed.

  Theorem ticket_already_in_range (id : lock_id) (k n i : Z) :
    ⌜i ∈ range k n⌝ -∗ ticket_range id k n -∗ ticket id i -∗ False.
  Proof.
    iIntros (Hi) "Hr Ht". rewrite ticket_range_eq /ticket_range_def.
    iDestruct (big_sepL_elem_of with "Hr") as "Ht'" => //.
    by iApply (ticket_non_duplicable with "Ht Ht'").
  Qed.

  Theorem overlaping_ticket_ranges (id : lock_id) (k1 k2 n1 n2 : Z) :
    ⌜∃ i, i ∈ range k1 n1 ∧ i ∈ range k2 n2⌝ -∗ ticket_range id k1 n1 -∗ ticket_range id k2 n2 -∗ False.
  Proof.
    iIntros ([i [??]]) "Hr1 Hr2". rewrite ticket_range_eq.
    iDestruct (big_sepL_elem_of with "Hr1") as "Ht1" => //.
    iDestruct (big_sepL_elem_of with "Hr2") as "Ht2" => //.
    by iApply (ticket_non_duplicable with "Ht1 Ht2").
  Qed.

  Theorem alloc_lock_token_aux :
    ⊢ |==> ∃ γ, lock_token_token γ [].
  Proof.
    iMod (own_alloc (● GSet ∅)) as (γ) "Hγ"; first by apply auth_auth_valid.
    iModIntro. iExists γ, ∅. by iFrame.
  Qed.

  Theorem alloc_tickets_aux_generic (ks : list Z) :
    Forall (λ i, i ≠ NO_TICKET) ks →
    NoDup ks →
    ⊢ |==> ∃ γ, [∗ list] i ∈ ks, ticket_aux γ i.
  Proof.
    move => Hks1 Hks2.
    iMod (own_alloc (list_to_map ((λ i, (i, Excl ())) <$> ks))) as (γ) "Hγ".
    { induction ks as [|k ks IH] => //=. apply insert_valid => //.
      apply Forall_cons in Hks1 as [Hk1 Hks1].
      apply NoDup_cons in Hks2 as [Hk2 Hks2].
      exact (IH Hks1 Hks2). }
    iModIntro. iExists γ. iInduction ks as [|k ks] "IH" => //=.
    apply Forall_cons in Hks1 as [Hk1 Hks1].
    apply NoDup_cons in Hks2 as [Hk2 Hks2].
    rewrite insert_singleton_op. iDestruct "Hγ" as "[$ Hks]".
    { iSplit; first done. by iApply "IH". }
    rewrite -/fmap /cmra_car /=. apply not_elem_of_list_to_map.
    by rewrite -list_fmap_compose elem_of_list_fmap_inj.
  Qed.

  Theorem alloc_tickets_aux :
    ⊢ |==> ∃ γ, [∗ list] i ∈ range 0 (LAST_TICKET + 1), ticket_aux γ i.
  Proof.
    iMod (alloc_tickets_aux_generic); last done.
    - apply Forall_seqZ. move => *. lia.
    - apply NoDup_seqZ.
  Qed.

  Theorem alloc_auth_owner (i : Z) :
    ⊢ |==> ∃ γ, owner_auth γ i ∗ owner_frag γ i.
  Proof.
    iMod (own_alloc (●E i ⋅ ◯E i)) as (γ) "H"; first by apply auth_both_valid.
    iExists γ. iModIntro. by iDestruct "H" as "[$ $]".
  Qed.

  Theorem owner_auth_update γ E (i j k : Z) :
    owner_auth γ i -∗ owner_frag γ j ={E}=∗ owner_auth γ k ∗ owner_frag γ k.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    rewrite /owner_auth /owner_frag -!own_op.
    iMod (own_update with "H"); last done. by apply excl_auth_update.
  Qed.

  Theorem owner_auth_agree γ (i j : Z) :
    owner_auth γ i -∗ owner_frag γ j -∗ ⌜i = j⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    by iDestruct (own_valid with "H") as %H%excl_auth_agree_L.
  Qed.

  Theorem alloc_lock_token_and_tickets :
    ⊢ |==> ∃ id, lock_token id [] ∗
                  ticket_range id 0 (LAST_TICKET + 1) ∗
                  owner_frag id.(γ_owner) 0.
  Proof.
    iMod (alloc_lock_token_aux) as (γl) "Hγl".
    iMod (alloc_tickets_aux) as (γt) "Hγt".
    iMod (alloc_auth_owner 0) as (γo) "[H● H◯]".
    iModIntro. iExists {|γ_lock := γl; γ_tickets := γt; γ_owner := γo|}.
    rewrite ticket_range_eq. iFrame "Hγt". eauto with iFrame.
  Qed.

  Global Instance inv_own_constraint (N : namespace) (P : iProp Σ):
    OwnConstraint (λ β, match β return _ with Own => P | Shr => inv N P end).
  Proof.
    constructor; first apply _.
    iIntros (??) "H". by iMod (inv_alloc with "H").
  Qed.

  Definition with_invariant (ty : type) (N : namespace) (P : iProp Σ) : type :=
    own_constrained (λ β, match β return _ with Own => P | Shr => inv N P end) ty.

  Definition hyp_spinlock_t_invariant (id : lock_id) (p1 p2 : loc) : iProp Σ := (
    ∃ owner next : Z,
      ⌜owner ≤ next ∧ owner ≠ NO_TICKET⌝ ∗
      p1 ◁ₗ owner @ int u16 ∗
      p2 ◁ₗ next  @ int u16 ∗
      owner_frag id.(γ_owner) owner ∗
      ticket_range id 0 owner ∗
      ticket_range id next (LAST_TICKET + 1) ∗
      ((ticket id owner ∧ ⌜owner < next⌝) ∨ lock_token id [])
  )%I.

  Global Instance hyp_spinlock_t_timeless id o n: Timeless (hyp_spinlock_t_invariant id o n).
  Proof. rewrite /hyp_spinlock_t_invariant /ty_own /=. apply _. Qed.

  Definition hyp_spinlock_t (id : lock_id) : type :=
    tyexists (λ p1, tyexists (λ p2,
      with_invariant (
        struct struct_hyp_spinlock [ place p1 ; place p2 ]
      ) lockN (hyp_spinlock_t_invariant id p1 p2)
    )).

  Program Definition spinlocked_ex {A} (id : lock_id) (n : string) (x : A) (ty : A → type) : type := {|
    ty_own β l :=
      match β return _ with
      | Own => l ◁ₗ ty x
      | Shr => ∃ γ', inv lockN ((∃ x', l ◁ₗ ty x' ∗ own γ' (Excl ())) ∨ own id.(γ_lock) (◯ GSet {[ n ]}))
      end
  |}%I.
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

  Lemma hyp_spinlock_t_subsume id1 id2 l T β:
    ⌜id1 = id2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} hyp_spinlock_t id1) (l ◁ₗ{β} hyp_spinlock_t id2) T.
  Proof. iIntros "[-> $] $". Qed.
  Global Instance spinlock_subsume_inst id1 id2 l β:
    Subsume (l ◁ₗ{β} hyp_spinlock_t id1) (l ◁ₗ{β} hyp_spinlock_t id2) :=
    λ T, i2p (hyp_spinlock_t_subsume id1 id2 l T β).

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

  Definition spinlocked_ex_token {A} (id : lock_id) (n : string) (l : loc) (β : own_state) (ty : A → type)  : iProp Σ :=
    (∀ E x, ⌜↑lockN ⊆ E⌝ -∗ l ◁ₗ ty x ={E}=∗ l ◁ₗ{β} spinlocked_ex id n x ty ∗ own id.(γ_lock) (◯ GSet {[ n ]}))%I.

  Lemma locked_open A n s l id (x : A) ty β E:
    n ∉ s → ↑lockN ⊆ E →
    l ◁ₗ{β} spinlocked_ex id n x ty -∗
      lock_token id s ={E}=∗
      ▷ ∃ x', l ◁ₗ ty x' ∗ lock_token id (n :: s) ∗ spinlocked_ex_token id n l β ty ∗ ⌜β = Own → x = x'⌝.
  Proof.
    iIntros (Hnotin ?) "Hl Hlock". iDestruct "Hlock" as (?) "[Hlock H●]".
    iDestruct "Hlock" as (st Hperm) "Hown". rewrite ->Hperm in Hnotin.
    iMod (own_update with "Hown") as "[Hown Hs]". { eapply auth_update_alloc.
      apply (gset_disj_alloc_empty_local_update st {[n]}). set_solver. }
    rewrite {1}/ty_own /=.
    iAssert (lock_token id (n :: s)) with "[Hown H●]" as "$". {
      iExists _. iFrame. iExists _. iFrame. iPureIntro.
      rewrite Hperm elements_union_singleton //. set_solver.
    }
    destruct β. { iIntros "!# !#". iExists _. iFrame. iSplit => //. eauto. }
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

  Lemma locked_close A n s l id (x : A) ty β E:
    ↑lockN ⊆ E →
    spinlocked_ex_token id n l β ty -∗ l ◁ₗ ty x -∗ lock_token id (n :: s) ={E}=∗
    lock_token id s ∗ l ◁ₗ{β} spinlocked_ex id n x ty.
  Proof.
    iIntros (HE) "Hlocked Hl Hlock".
    iMod ("Hlocked" with "[//] Hl") as "[$ Hn]".
    iDestruct "Hlock" as (?) "[Hlock ?]".
    iDestruct "Hlock" as (st Hst) "Htok".
    iExists _. iFrame.
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

  Lemma annot_unlock A l T β id n ty (x : A):
    (find_in_context (FindDirect (lock_token id)) (λ s : list string, ⌜n∉s⌝ ∗ (∀ x',
        lock_token id (n :: s) -∗ spinlocked_ex_token id n l β ty -∗ ⌜β = Own → x = x'⌝ -∗
                       l ◁ₗ ty x' -∗ T))) -∗
    typed_annot_stmt UnlockA l β (spinlocked_ex id n x ty) T.
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
    (∃ β id, subsume (l ◁ᵥ ty) (l ◁ₗ{β} hyp_spinlock_t id) (
      find_in_context (FindDirect (lock_token id)) (λ s : list string, foldr (λ t T,
        find_in_context (FindDirect (λ '(existT A (l2, ty)), spinlocked_ex_token (A:=A) id t l2 β ty)) (λ '(existT A (l2, ty)), ∃ x,
          l2 ◁ₗ ty x ∗ (l2 ◁ₗ{β} spinlocked_ex id t x ty -∗ T))) (l ◁ₗ{β} hyp_spinlock_t id -∗ lock_token id [] -∗ T) s))) -∗
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
Typeclasses Opaque hyp_spinlock_t spinlocked_ex lock_token spinlocked_ex_token.
Notation spinlocked γ n ty := (spinlocked_ex γ n tt (λ _, ty)).
Notation spinlocked_token γ n l β ty := (spinlocked_ex_token γ n l β (λ _ : unit, ty)).
