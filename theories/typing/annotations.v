From refinedc.typing Require Import base.

Inductive to_uninit_annot : Type :=
  ToUninit.

Inductive uninit_strengthen_align_annot : Type :=
  UninitStrengthenAlign.

Inductive stop_annot : Type :=
  StopAnnot.

Inductive share_annot : Type :=
  ShareAnnot.

Inductive unfold_once_annot : Type :=
  UnfoldOnceAnnot.

Inductive learn_annot : Type :=
  LearnAnnot.

Inductive learn_alignment_annot : Type :=
  LearnAlignmentAnnot.

Inductive LockAnnot : Type := LockA | UnlockA.
