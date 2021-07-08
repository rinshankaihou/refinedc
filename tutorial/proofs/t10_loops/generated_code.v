From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t10_loops.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t10_loops.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 7 2 7 18.
  Definition loc_12 : location_info := LocationInfo file_1 10 2 10 18.
  Definition loc_13 : location_info := LocationInfo file_1 13 2 13 18.
  Definition loc_14 : location_info := LocationInfo file_1 13 2 13 18.
  Definition loc_15 : location_info := LocationInfo file_1 13 16 13 18.
  Definition loc_16 : location_info := LocationInfo file_1 13 2 13 18.
  Definition loc_17 : location_info := LocationInfo file_1 13 2 13 18.
  Definition loc_18 : location_info := LocationInfo file_1 13 8 13 14.
  Definition loc_19 : location_info := LocationInfo file_1 13 8 13 9.
  Definition loc_20 : location_info := LocationInfo file_1 13 8 13 9.
  Definition loc_21 : location_info := LocationInfo file_1 13 13 13 14.
  Definition loc_22 : location_info := LocationInfo file_1 10 2 10 18.
  Definition loc_23 : location_info := LocationInfo file_1 10 16 10 18.
  Definition loc_24 : location_info := LocationInfo file_1 10 2 10 18.
  Definition loc_25 : location_info := LocationInfo file_1 10 2 10 18.
  Definition loc_26 : location_info := LocationInfo file_1 10 8 10 14.
  Definition loc_27 : location_info := LocationInfo file_1 10 8 10 9.
  Definition loc_28 : location_info := LocationInfo file_1 10 8 10 9.
  Definition loc_29 : location_info := LocationInfo file_1 10 13 10 14.
  Definition loc_30 : location_info := LocationInfo file_1 7 2 7 18.
  Definition loc_31 : location_info := LocationInfo file_1 7 16 7 18.
  Definition loc_32 : location_info := LocationInfo file_1 7 2 7 18.
  Definition loc_33 : location_info := LocationInfo file_1 7 2 7 18.
  Definition loc_34 : location_info := LocationInfo file_1 7 8 7 14.
  Definition loc_35 : location_info := LocationInfo file_1 7 8 7 9.
  Definition loc_36 : location_info := LocationInfo file_1 7 8 7 9.
  Definition loc_37 : location_info := LocationInfo file_1 7 13 7 14.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [loop_without_annot]. *)
  Definition impl_loop_without_annot : function := {|
    f_args := [
      ("a", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_34 ;
        if: LocInfoE loc_34 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_34 ((LocInfoE loc_35 (use{it_layout i32} (LocInfoE loc_36 ("a")))) ={IntOp i32, IntOp i32} (LocInfoE loc_37 (i2v 1 i32)))))
        then
        locinfo: loc_32 ;
          Goto "#2"
        else
        locinfo: loc_12 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_32 ;
        Goto "continue4"
      ]> $
      <[ "#3" :=
        locinfo: loc_12 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_26 ;
        if: LocInfoE loc_26 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_26 ((LocInfoE loc_27 (use{it_layout i32} (LocInfoE loc_28 ("a")))) ={IntOp i32, IntOp i32} (LocInfoE loc_29 (i2v 1 i32)))))
        then
        locinfo: loc_24 ;
          Goto "#5"
        else
        locinfo: loc_13 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_24 ;
        Goto "continue6"
      ]> $
      <[ "#6" :=
        locinfo: loc_13 ;
        Goto "#7"
      ]> $
      <[ "#7" :=
        locinfo: loc_18 ;
        if: LocInfoE loc_18 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_18 ((LocInfoE loc_19 (use{it_layout i32} (LocInfoE loc_20 ("a")))) ={IntOp i32, IntOp i32} (LocInfoE loc_21 (i2v 1 i32)))))
        then
        locinfo: loc_16 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_16 ;
        Goto "continue8"
      ]> $
      <[ "#9" :=
        Return (VOID)
      ]> $
      <[ "continue4" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "continue6" :=
        locinfo: loc_12 ;
        Goto "#4"
      ]> $
      <[ "continue8" :=
        locinfo: loc_13 ;
        Goto "#7"
      ]> $∅
    )%E
  |}.
End code.
