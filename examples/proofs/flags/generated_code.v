From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/flags.c]. *)
Section code.
  Definition file_0 : string := "examples/flags.c".
  Definition loc_2 : location_info := LocationInfo file_0 32 2 32 21.
  Definition loc_3 : location_info := LocationInfo file_0 33 2 33 41.
  Definition loc_4 : location_info := LocationInfo file_0 34 2 34 41.
  Definition loc_5 : location_info := LocationInfo file_0 35 2 35 11.
  Definition loc_6 : location_info := LocationInfo file_0 35 9 35 10.
  Definition loc_7 : location_info := LocationInfo file_0 35 9 35 10.
  Definition loc_8 : location_info := LocationInfo file_0 34 31 34 41.
  Definition loc_9 : location_info := LocationInfo file_0 34 31 34 32.
  Definition loc_10 : location_info := LocationInfo file_0 34 31 34 40.
  Definition loc_11 : location_info := LocationInfo file_0 34 31 34 32.
  Definition loc_12 : location_info := LocationInfo file_0 34 31 34 32.
  Definition loc_13 : location_info := LocationInfo file_0 34 36 34 40.
  Definition loc_14 : location_info := LocationInfo file_0 34 36 34 40.
  Definition loc_15 : location_info := LocationInfo file_0 34 2 34 41.
  Definition loc_16 : location_info := LocationInfo file_0 34 5 34 29.
  Definition loc_17 : location_info := LocationInfo file_0 34 6 34 24.
  Definition loc_18 : location_info := LocationInfo file_0 34 7 34 16.
  Definition loc_19 : location_info := LocationInfo file_0 34 7 34 16.
  Definition loc_20 : location_info := LocationInfo file_0 34 7 34 10.
  Definition loc_21 : location_info := LocationInfo file_0 34 20 34 23.
  Definition loc_22 : location_info := LocationInfo file_0 34 27 34 28.
  Definition loc_23 : location_info := LocationInfo file_0 33 31 33 41.
  Definition loc_24 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_25 : location_info := LocationInfo file_0 33 31 33 40.
  Definition loc_26 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_27 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_28 : location_info := LocationInfo file_0 33 36 33 40.
  Definition loc_29 : location_info := LocationInfo file_0 33 36 33 40.
  Definition loc_30 : location_info := LocationInfo file_0 33 2 33 41.
  Definition loc_31 : location_info := LocationInfo file_0 33 5 33 29.
  Definition loc_32 : location_info := LocationInfo file_0 33 6 33 24.
  Definition loc_33 : location_info := LocationInfo file_0 33 7 33 16.
  Definition loc_34 : location_info := LocationInfo file_0 33 7 33 16.
  Definition loc_35 : location_info := LocationInfo file_0 33 7 33 10.
  Definition loc_36 : location_info := LocationInfo file_0 33 20 33 23.
  Definition loc_37 : location_info := LocationInfo file_0 33 27 33 28.
  Definition loc_38 : location_info := LocationInfo file_0 32 19 32 20.

  (* Definition of struct [flags]. *)
  Program Definition struct_flags := {|
    sl_members := [
      (Some "flags", it_layout u8)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [sum]. *)
  Definition impl_sum : function := {|
    f_args := [
      ("f", layout_of struct_flags);
      ("arg1", it_layout u32);
      ("arg2", it_layout u32)
    ];
    f_local_vars := [
      ("r", it_layout u32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "r" <-{ IntOp u32 }
          LocInfoE loc_38 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_38 (i2v 0 i32))) ;
        locinfo: loc_31 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_31 ((LocInfoE loc_32 ((LocInfoE loc_33 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_33 (use{IntOp u8} (LocInfoE loc_34 ((LocInfoE loc_35 ("f")) at{struct_flags} "flags")))))) >>{IntOp i32, IntOp i32} (LocInfoE loc_36 (i2v 0 i32)))) &{IntOp i32, IntOp i32} (LocInfoE loc_37 (i2v 1 i32)))
        then
        locinfo: loc_23 ;
          Goto "#5"
        else
        locinfo: loc_16 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_16 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_16 ((LocInfoE loc_17 ((LocInfoE loc_18 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_18 (use{IntOp u8} (LocInfoE loc_19 ((LocInfoE loc_20 ("f")) at{struct_flags} "flags")))))) >>{IntOp i32, IntOp i32} (LocInfoE loc_21 (i2v 1 i32)))) &{IntOp i32, IntOp i32} (LocInfoE loc_22 (i2v 1 i32)))
        then
        locinfo: loc_8 ;
          Goto "#3"
        else
        locinfo: loc_5 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_5 ;
        Return (LocInfoE loc_6 (use{IntOp u32} (LocInfoE loc_7 ("r"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_8 ;
        LocInfoE loc_9 ("r") <-{ IntOp u32 }
          LocInfoE loc_10 ((LocInfoE loc_11 (use{IntOp u32} (LocInfoE loc_12 ("r")))) +{IntOp u32, IntOp u32} (LocInfoE loc_13 (use{IntOp u32} (LocInfoE loc_14 ("arg2"))))) ;
        locinfo: loc_5 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_5 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_23 ;
        LocInfoE loc_24 ("r") <-{ IntOp u32 }
          LocInfoE loc_25 ((LocInfoE loc_26 (use{IntOp u32} (LocInfoE loc_27 ("r")))) +{IntOp u32, IntOp u32} (LocInfoE loc_28 (use{IntOp u32} (LocInfoE loc_29 ("arg1"))))) ;
        locinfo: loc_16 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_16 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
