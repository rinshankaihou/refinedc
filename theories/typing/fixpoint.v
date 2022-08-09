From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes.
Set Default Proof Using "Type*".
Import uPred.


Section fixpoint.
  Context `{!typeG Σ}.

  (* TODO: Is it possible to use monotone fixpoints instead of guarded
  fixpoints here? It is not obvious how to do that since the Iris
  monotone fixpoint library is for BIs, not for OFEs. Maybe it could
  work to make ty_own_val and ty_has_op_type trivial (as currently in
  guarded)? This would be quite annoying as it would mean that
  fixpoints are not movable. But maybe one can work around this
  problem by unfolding the T once in the definition of the fixpoint
  and making sure that the recursive occurence occurs under a pointer
  such that it's ty_own is used which can be unfolded? I.e. something
  like the following:

   list_t_rec R := optional (&own R) null

   list_t := list_t_rec (fixp R)

  with ty_own (fixp R) β l ≡ ty_own (R (fixp R)) β l

  Not sure if this would actually work, in particular if one can show
  that fixp is a type. Maybe if one makes sharing trivial as well?
 *)

  Global Instance type_inhabited : Inhabited type := populate (uninit void_layout).

  Context {A : Type} (T : (A -d> typeO) → (A -d> typeO)) {HT: Contractive T}.

  Definition type_fixpoint : (A -d> typeO) → (A -d> typeO) := (λ self, T (λ x, apply_dfun self x)).
  Global Instance type_fixpoint_contractive : Contractive type_fixpoint.
  Proof.
    constructor; intros.
    - eapply ty_has_op_type_ne => //. apply HT. solve_contractive.
    - apply ty_own_ne => //. apply HT. solve_contractive.
    - apply ty_own_val_ne => //. apply HT. solve_contractive.
  Qed.


  Definition fixp := (apply_dfun (fixpoint type_fixpoint)).

  Lemma fixp_unfold n:
    fixp n ≡ T (λ n, fixp n) n.
  Proof. rewrite /fixp. rewrite ->fixpoint_unfold. rewrite /apply_dfun{1}/type_fixpoint. f_equiv. Qed.

  Lemma fixp_unfold' x:
    T fixp x ≡@{type} T (T fixp) x.
  Proof. apply (contractive_proper T) => ?. by rewrite -fixp_unfold. Qed.
End fixpoint.

Section fixpoint.
  Context `{!typeG Σ}.
  Lemma fixp_proper {A} x1 x2 (T1 T2 : (A -d> typeO) → (A -d> typeO)) `{!Contractive T1} `{!Contractive T2}:
    x1 = x2 → (∀ f x, T1 f x ≡ T2 f x) →
    fixp T1 x1 ≡ fixp T2 x2.
  Proof.
    move => ? HT. rewrite /fixp.
    apply apply_dfun_proper => //.
    apply fixpoint_proper => ?.
    rewrite /type_fixpoint.
    apply: HT.
  Qed.
End fixpoint.

(*** Tests *)
Section tests.
  Context `{!typeG Σ}.
  Context (own_ptr : type → type) {HT: NonExpansive own_ptr}.

  Definition fixpoint_test_rec : (nat -d> typeO) → (nat -d> typeO) := (λ self, λ n, own_ptr (guarded ("test") (apply_dfun self (S n)))).
  Arguments fixpoint_test_rec /.
  Global Instance fixpoint_test_rec_ne : Contractive fixpoint_test_rec.
  Proof. solve_type_proper. Qed.

  Definition fixpoint_test : rtype := {|
    rty_type := nat;
    rty n := fixp fixpoint_test_rec n
  |}.

  Example test l :
    l◁ₗ 0%nat @ fixpoint_test -∗ True.
  Proof.
    simpl. rewrite /with_refinement/= fixp_unfold/apply_dfun/=.
    change (fixp _ _) with (1%nat @ fixpoint_test)%I.
  Abort.

End tests.
