From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t10_loops.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t10_loops.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 7 2 7 8.
  Definition loc_12 : location_info := LocationInfo file_1 8 2 8 18.
  Definition loc_13 : location_info := LocationInfo file_1 11 2 11 18.
  Definition loc_14 : location_info := LocationInfo file_1 14 2 14 18.
  Definition loc_15 : location_info := LocationInfo file_1 14 16 14 18.
  Definition loc_16 : location_info := LocationInfo file_1 14 8 14 14.
  Definition loc_17 : location_info := LocationInfo file_1 14 8 14 9.
  Definition loc_18 : location_info := LocationInfo file_1 14 8 14 9.
  Definition loc_19 : location_info := LocationInfo file_1 14 13 14 14.
  Definition loc_20 : location_info := LocationInfo file_1 11 16 11 18.
  Definition loc_21 : location_info := LocationInfo file_1 11 8 11 14.
  Definition loc_22 : location_info := LocationInfo file_1 11 8 11 9.
  Definition loc_23 : location_info := LocationInfo file_1 11 8 11 9.
  Definition loc_24 : location_info := LocationInfo file_1 11 13 11 14.
  Definition loc_25 : location_info := LocationInfo file_1 8 16 8 18.
  Definition loc_26 : location_info := LocationInfo file_1 8 8 8 14.
  Definition loc_27 : location_info := LocationInfo file_1 8 8 8 9.
  Definition loc_28 : location_info := LocationInfo file_1 8 8 8 9.
  Definition loc_29 : location_info := LocationInfo file_1 8 13 8 14.

  (* Definition of function [copy_alloc_id]. *)
  Definition impl_copy_alloc_id : function := {|
    f_args := [
      ("to", it_layout uintptr_t);
      ("from", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{IntOp uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{PtrOp} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [loop_without_annot]. *)
  Definition impl_loop_without_annot : function := {|
    f_args := [
      ("a", it_layout i32);
      ("b", it_layout i32);
      ("c", it_layout i32)
    ];
    f_local_vars := [
      ("z", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_12 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_26 ;
        if{IntOp i32, None}: LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp i32} (LocInfoE loc_28 ("a")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_29 (i2v 1 i32)))
        then
        locinfo: loc_12 ;
          Goto "#2"
        else
        locinfo: loc_13 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_12 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_13 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_21 ;
        if{IntOp i32, None}: LocInfoE loc_21 ((LocInfoE loc_22 (use{IntOp i32} (LocInfoE loc_23 ("b")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_24 (i2v 1 i32)))
        then
        locinfo: loc_13 ;
          Goto "#5"
        else
        locinfo: loc_14 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_13 ;
        Goto "#4"
      ]> $
      <[ "#6" :=
        locinfo: loc_14 ;
        Goto "#7"
      ]> $
      <[ "#7" :=
        locinfo: loc_16 ;
        if{IntOp i32, None}: LocInfoE loc_16 ((LocInfoE loc_17 (use{IntOp i32} (LocInfoE loc_18 ("c")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_19 (i2v 1 i32)))
        then
        locinfo: loc_14 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_14 ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
