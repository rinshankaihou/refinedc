From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import generated_code.
Set Default Proof Using "Type".

Section type.
  Context `{!typeG Σ} `{!lockG Σ}.

  Definition spinlock (γ : lock_id) : type :=
    struct struct_spinlock [atomic_bool u8 True (lock_token γ [])].

  Global Program Instance movable_spinlock γ : Movable (spinlock γ) := ltac:(apply: movable_struct).

  Global Instance alloc_alive_spinlock γ β : AllocAlive (spinlock γ) β True.
  Proof. apply: _. Qed.

  Lemma spinlock_subsume γ1 γ2 l T β:
    ⌜γ1 = γ2⌝ ∗ T -∗
    subsume (l ◁ₗ{β} spinlock γ1) (l ◁ₗ{β} spinlock γ2) T.
  Proof. iIntros "[-> $] $". Qed.
  Global Instance spinlock_subsume_inst γ1 γ2 l β:
    Subsume (l ◁ₗ{β} spinlock γ1) (l ◁ₗ{β} spinlock γ2) :=
    λ T, i2p (spinlock_subsume γ1 γ2 l T β).

  Global Instance spinlock_with_lock_id γ : WithLockId (spinlock γ) γ := I.
End type.

Typeclasses Opaque spinlock.
