From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t10_loops.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/t10_loops.c".
  Definition loc_2 : location_info := LocationInfo file_0 7 2 7 18.
  Definition loc_3 : location_info := LocationInfo file_0 10 2 10 18.
  Definition loc_4 : location_info := LocationInfo file_0 13 2 13 18.
  Definition loc_5 : location_info := LocationInfo file_0 13 2 13 18.
  Definition loc_6 : location_info := LocationInfo file_0 13 16 13 18.
  Definition loc_7 : location_info := LocationInfo file_0 13 2 13 18.
  Definition loc_8 : location_info := LocationInfo file_0 13 2 13 18.
  Definition loc_9 : location_info := LocationInfo file_0 13 8 13 14.
  Definition loc_10 : location_info := LocationInfo file_0 13 8 13 9.
  Definition loc_11 : location_info := LocationInfo file_0 13 8 13 9.
  Definition loc_12 : location_info := LocationInfo file_0 13 13 13 14.
  Definition loc_13 : location_info := LocationInfo file_0 10 2 10 18.
  Definition loc_14 : location_info := LocationInfo file_0 10 16 10 18.
  Definition loc_15 : location_info := LocationInfo file_0 10 2 10 18.
  Definition loc_16 : location_info := LocationInfo file_0 10 2 10 18.
  Definition loc_17 : location_info := LocationInfo file_0 10 8 10 14.
  Definition loc_18 : location_info := LocationInfo file_0 10 8 10 9.
  Definition loc_19 : location_info := LocationInfo file_0 10 8 10 9.
  Definition loc_20 : location_info := LocationInfo file_0 10 13 10 14.
  Definition loc_21 : location_info := LocationInfo file_0 7 2 7 18.
  Definition loc_22 : location_info := LocationInfo file_0 7 16 7 18.
  Definition loc_23 : location_info := LocationInfo file_0 7 2 7 18.
  Definition loc_24 : location_info := LocationInfo file_0 7 2 7 18.
  Definition loc_25 : location_info := LocationInfo file_0 7 8 7 14.
  Definition loc_26 : location_info := LocationInfo file_0 7 8 7 9.
  Definition loc_27 : location_info := LocationInfo file_0 7 8 7 9.
  Definition loc_28 : location_info := LocationInfo file_0 7 13 7 14.

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
        locinfo: loc_2 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_25 ;
        if: LocInfoE loc_25 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_25 ((LocInfoE loc_26 (use{it_layout i32} (LocInfoE loc_27 ("a")))) ={IntOp i32, IntOp i32} (LocInfoE loc_28 (i2v 1 i32)))))
        then
        locinfo: loc_23 ;
          Goto "#2"
        else
        locinfo: loc_3 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_23 ;
        Goto "continue2"
      ]> $
      <[ "#3" :=
        locinfo: loc_3 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_17 ;
        if: LocInfoE loc_17 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_17 ((LocInfoE loc_18 (use{it_layout i32} (LocInfoE loc_19 ("a")))) ={IntOp i32, IntOp i32} (LocInfoE loc_20 (i2v 1 i32)))))
        then
        locinfo: loc_15 ;
          Goto "#5"
        else
        locinfo: loc_4 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_15 ;
        Goto "continue4"
      ]> $
      <[ "#6" :=
        locinfo: loc_4 ;
        Goto "#7"
      ]> $
      <[ "#7" :=
        locinfo: loc_9 ;
        if: LocInfoE loc_9 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_9 ((LocInfoE loc_10 (use{it_layout i32} (LocInfoE loc_11 ("a")))) ={IntOp i32, IntOp i32} (LocInfoE loc_12 (i2v 1 i32)))))
        then
        locinfo: loc_7 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_7 ;
        Goto "continue6"
      ]> $
      <[ "#9" :=
        Return (VOID)
      ]> $
      <[ "continue2" :=
        locinfo: loc_2 ;
        Goto "#1"
      ]> $
      <[ "continue4" :=
        locinfo: loc_3 ;
        Goto "#4"
      ]> $
      <[ "continue6" :=
        locinfo: loc_4 ;
        Goto "#7"
      ]> $∅
    )%E
  |}.
End code.
