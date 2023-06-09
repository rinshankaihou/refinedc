From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export gen_heap.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From lithium.tutorial Require Export lang notation.

Class tutorialGS (Σ : gFunctors) := TutorialGS {
    tutorial_invGS : invGS Σ;
    tutorial_gen_heapGS :: gen_heapGS loc val Σ;
}.

Global Instance tutorial_irisG `{!tutorialGS Σ} : irisGS tutorial_lang Σ := {
  iris_invGS := tutorial_invGS;
  state_interp σ κs _ _ := gen_heap_interp σ.(heap);
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

Notation "l ↦ dq v" := (mapsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.
