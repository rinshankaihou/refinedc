From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section zeroed.
  Context `{!typeG Σ}.

  Program Definition zeroed (ly : layout) : type := {|
    ty_own β l := (⌜l `has_layout_loc` ly⌝ ∗ l ↦[β] zero_val ly.(ly_size))%I;
  |}.
  Next Obligation. iIntros (????) "[% ?]". iSplitR => //. by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance movable_zeroed ly : Movable (zeroed ly) := {|
    ty_layout := ly;
    ty_own_val v := ⌜v = zero_val ly.(ly_size)⌝%I;
  |}.
  Next Obligation. iIntros (ly l). by iDestruct 1 as (?) "?". Qed.
  Next Obligation. iIntros (ly v ->). by rewrite /has_layout_val replicate_length. Qed.
  Next Obligation. iIntros (ly l) "[% Hl]". eauto with iFrame. Qed.
  Next Obligation. iIntros (ly l v ?) "Hl ->". by iFrame. Qed.

  Lemma zeroed_loc_in_bounds l β ly :
    l ◁ₗ{β} zeroed ly -∗ loc_in_bounds l (ly_size ly).
  Proof.
    iIntros "[% Hl]". iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hl".
    by rewrite replicate_length.
  Qed.

  Global Instance loc_in_bounds_zeroed ly β: LocInBounds (zeroed ly) β (ly_size ly).
  Proof.
    constructor. iIntros (l) "Hl".
    iDestruct (zeroed_loc_in_bounds with "Hl") as "#Hb".
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.
End zeroed.
Notation "zeroed< ly >" := (zeroed ly)
  (only printing, format "'zeroed<' ly '>'") : printing_sugar.
