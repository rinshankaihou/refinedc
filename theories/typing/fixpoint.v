From refinedc.typing Require Export type.
From refinedc.typing Require Import programs uninit.
Set Default Proof Using "Type*".
Import uPred.


Section fixpoint.
  Context `{!typeG Σ}.

  Global Instance type_inhabited : Inhabited type := populate (uninit LVoid).

  Context {A : Type} (T : (A -d> typeO) → (A -d> typeO)) {HT: Contractive T}.

  Definition type_fixpoint : (A -d> typeO) → (A -d> typeO) := (λ self, T (λ x, apply_dfun self x)).
  Global Instance type_fixpoint_contractive : Contractive type_fixpoint.
  Proof. constructor. intros. apply ty_own_ne => //. apply HT. solve_contractive. Qed.


  Definition fixp := (apply_dfun (fixpoint type_fixpoint)).

  Lemma fixp_unfold n:
    fixp n ≡ T (λ n, fixp n) n.
  Proof. rewrite /fixp. rewrite ->fixpoint_unfold. rewrite /apply_dfun{1}/type_fixpoint. f_equiv. Qed.

End fixpoint.

(*** Tests *)
Section tests.
  Context `{!typeG Σ}.
  Context (own_ptr : type → type) {HT: NonExpansive own_ptr}.

  Definition fixpoint_test_rec : (nat -d> typeO) → (nat -d> typeO) := (λ self, λ n, own_ptr (guarded ("test") (apply_dfun self (S n)))).
  Arguments fixpoint_test_rec /.
  Global Instance fixpoint_test_rec_ne : Contractive fixpoint_test_rec.
  Proof.
    constructor => ??. f_equiv => /=. f_equiv. f_contractive. done.
  Qed.

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
