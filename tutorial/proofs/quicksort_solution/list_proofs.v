From refinedc.typing Require Import typing.
Set Default Proof Using "Type".

Section filter_proof.
  Context {A : Type}.
  Implicit Types (P : A → Prop).

  Lemma filter_permutation xs P P' `{∀ x, Decision (P' x), ∀ x, Decision (P x)}: 
    (∀ x, ¬ P x ↔ P' x) →
    xs ≡ₚ filter P xs ++ filter P' xs.
  Proof.
    move => HPP'.
    induction xs as [|a xs IHxs] => //.
    rewrite !filter_cons.
    destruct (decide (P a)) as [HP | HnP].
    + rewrite decide_False; [ | contradict HP; by apply HPP'].
      apply perm_skip, IHxs.
    + rewrite decide_True; [ | by apply HPP'].
      rewrite -Permutation_middle.
      apply perm_skip, IHxs.
  Qed.

  Lemma Forall_filter xs P P' `{∀ x, Decision (P' x)} :
    (∀ x, P' x → P x) →
    Forall P (filter P' xs).
  Proof.
    move => HPP'.
    induction xs as [|a xs IHxs].
    + by rewrite filter_nil.
    + rewrite filter_cons.
      destruct (decide _) => //.
      apply Forall_cons; split => //.
      by apply HPP'.
  Qed.

End filter_proof.

Section sorted_list_proof.
  Context {A : Type}.
  Context (R : A → A → Prop).

  Lemma sorted_append_middle_el xs ys m:
    Transitive R →
    Sorted R xs →
    Sorted R ys →
    Forall (λ e, R e m) xs →
    Forall (λ e, R m e) ys →
    Sorted R (xs ++ ys).
  Proof.
    move => H /Sorted_StronglySorted H1 /Sorted_StronglySorted H2 Hxs Hys.
    apply StronglySorted_Sorted.
    induction xs as [|a xs IHxs] => //=.
    inversion Hxs. apply SSorted_cons.
    + apply: IHxs => //.
      by eapply StronglySorted_inv.
    + apply Forall_app_2; first by apply StronglySorted_inv.
      eapply Forall_impl => //= x3.
      by apply H.
  Qed.

End sorted_list_proof.

Ltac list_perm_subst := 
  match goal with 
  | H: ?listL ≡ₚ ?listR |- ?P => (rewrite H => {H} || rewrite -H => {H})
  end.
