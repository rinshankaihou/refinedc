From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [theories/examples/misc/flags.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/misc/flags.c".
  Definition loc_2 : location_info := LocationInfo file_0 38 2 38 21.
  Definition loc_3 : location_info := LocationInfo file_0 39 2 39 46.
  Definition loc_4 : location_info := LocationInfo file_0 40 2 40 46.
  Definition loc_5 : location_info := LocationInfo file_0 41 2 41 46.
  Definition loc_6 : location_info := LocationInfo file_0 42 2 42 11.
  Definition loc_7 : location_info := LocationInfo file_0 42 9 42 10.
  Definition loc_8 : location_info := LocationInfo file_0 42 9 42 10.
  Definition loc_9 : location_info := LocationInfo file_0 41 36 41 46.
  Definition loc_10 : location_info := LocationInfo file_0 41 36 41 37.
  Definition loc_11 : location_info := LocationInfo file_0 41 36 41 45.
  Definition loc_12 : location_info := LocationInfo file_0 41 36 41 37.
  Definition loc_13 : location_info := LocationInfo file_0 41 36 41 37.
  Definition loc_14 : location_info := LocationInfo file_0 41 41 41 45.
  Definition loc_15 : location_info := LocationInfo file_0 41 41 41 45.
  Definition loc_17 : location_info := LocationInfo file_0 41 5 41 34.
  Definition loc_18 : location_info := LocationInfo file_0 41 6 41 28.
  Definition loc_19 : location_info := LocationInfo file_0 41 6 41 24.
  Definition loc_20 : location_info := LocationInfo file_0 41 7 41 16.
  Definition loc_21 : location_info := LocationInfo file_0 41 7 41 16.
  Definition loc_22 : location_info := LocationInfo file_0 41 7 41 10.
  Definition loc_23 : location_info := LocationInfo file_0 41 20 41 23.
  Definition loc_24 : location_info := LocationInfo file_0 41 27 41 28.
  Definition loc_25 : location_info := LocationInfo file_0 41 32 41 33.
  Definition loc_26 : location_info := LocationInfo file_0 40 36 40 46.
  Definition loc_27 : location_info := LocationInfo file_0 40 36 40 37.
  Definition loc_28 : location_info := LocationInfo file_0 40 36 40 45.
  Definition loc_29 : location_info := LocationInfo file_0 40 36 40 37.
  Definition loc_30 : location_info := LocationInfo file_0 40 36 40 37.
  Definition loc_31 : location_info := LocationInfo file_0 40 41 40 45.
  Definition loc_32 : location_info := LocationInfo file_0 40 41 40 45.
  Definition loc_34 : location_info := LocationInfo file_0 40 5 40 34.
  Definition loc_35 : location_info := LocationInfo file_0 40 6 40 28.
  Definition loc_36 : location_info := LocationInfo file_0 40 6 40 24.
  Definition loc_37 : location_info := LocationInfo file_0 40 7 40 16.
  Definition loc_38 : location_info := LocationInfo file_0 40 7 40 16.
  Definition loc_39 : location_info := LocationInfo file_0 40 7 40 10.
  Definition loc_40 : location_info := LocationInfo file_0 40 20 40 23.
  Definition loc_41 : location_info := LocationInfo file_0 40 27 40 28.
  Definition loc_42 : location_info := LocationInfo file_0 40 32 40 33.
  Definition loc_43 : location_info := LocationInfo file_0 39 36 39 46.
  Definition loc_44 : location_info := LocationInfo file_0 39 36 39 37.
  Definition loc_45 : location_info := LocationInfo file_0 39 36 39 45.
  Definition loc_46 : location_info := LocationInfo file_0 39 36 39 37.
  Definition loc_47 : location_info := LocationInfo file_0 39 36 39 37.
  Definition loc_48 : location_info := LocationInfo file_0 39 41 39 45.
  Definition loc_49 : location_info := LocationInfo file_0 39 41 39 45.
  Definition loc_51 : location_info := LocationInfo file_0 39 5 39 34.
  Definition loc_52 : location_info := LocationInfo file_0 39 6 39 28.
  Definition loc_53 : location_info := LocationInfo file_0 39 6 39 24.
  Definition loc_54 : location_info := LocationInfo file_0 39 7 39 16.
  Definition loc_55 : location_info := LocationInfo file_0 39 7 39 16.
  Definition loc_56 : location_info := LocationInfo file_0 39 7 39 10.
  Definition loc_57 : location_info := LocationInfo file_0 39 20 39 23.
  Definition loc_58 : location_info := LocationInfo file_0 39 27 39 28.
  Definition loc_59 : location_info := LocationInfo file_0 39 32 39 33.
  Definition loc_60 : location_info := LocationInfo file_0 38 19 38 20.

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
      ("arg2", it_layout u32);
      ("arg3", it_layout u32)
    ];
    f_local_vars := [
      ("r", it_layout u32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "r" <-{ it_layout u32 }
          LocInfoE loc_60 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_60 (i2v 0 i32))) ;
        locinfo: loc_51 ;
        if: LocInfoE loc_51 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_51 ((LocInfoE loc_52 ((LocInfoE loc_53 ((LocInfoE loc_54 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_54 (use{it_layout u8} (LocInfoE loc_55 ((LocInfoE loc_56 ("f")) at{struct_flags} "flags")))))) >>{IntOp i32, IntOp i32} (LocInfoE loc_57 (i2v 0 i32)))) %{IntOp i32, IntOp i32} (LocInfoE loc_58 (i2v 2 i32)))) ={IntOp i32, IntOp i32} (LocInfoE loc_59 (i2v 1 i32)))))
        then
        locinfo: loc_43 ;
          Goto "#8"
        else
        locinfo: loc_34 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_34 ;
        if: LocInfoE loc_34 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_34 ((LocInfoE loc_35 ((LocInfoE loc_36 ((LocInfoE loc_37 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_37 (use{it_layout u8} (LocInfoE loc_38 ((LocInfoE loc_39 ("f")) at{struct_flags} "flags")))))) >>{IntOp i32, IntOp i32} (LocInfoE loc_40 (i2v 1 i32)))) %{IntOp i32, IntOp i32} (LocInfoE loc_41 (i2v 2 i32)))) ={IntOp i32, IntOp i32} (LocInfoE loc_42 (i2v 1 i32)))))
        then
        locinfo: loc_26 ;
          Goto "#6"
        else
        locinfo: loc_17 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_17 ;
        if: LocInfoE loc_17 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_17 ((LocInfoE loc_18 ((LocInfoE loc_19 ((LocInfoE loc_20 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_20 (use{it_layout u8} (LocInfoE loc_21 ((LocInfoE loc_22 ("f")) at{struct_flags} "flags")))))) >>{IntOp i32, IntOp i32} (LocInfoE loc_23 (i2v 2 i32)))) %{IntOp i32, IntOp i32} (LocInfoE loc_24 (i2v 2 i32)))) ={IntOp i32, IntOp i32} (LocInfoE loc_25 (i2v 1 i32)))))
        then
        locinfo: loc_9 ;
          Goto "#4"
        else
        locinfo: loc_6 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_6 ;
        Return (LocInfoE loc_7 (use{it_layout u32} (LocInfoE loc_8 ("r"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_9 ;
        LocInfoE loc_10 ("r") <-{ it_layout u32 }
          LocInfoE loc_11 ((LocInfoE loc_12 (use{it_layout u32} (LocInfoE loc_13 ("r")))) +{IntOp u32, IntOp u32} (LocInfoE loc_14 (use{it_layout u32} (LocInfoE loc_15 ("arg3"))))) ;
        locinfo: loc_6 ;
        Goto "#3"
      ]> $
      <[ "#5" :=
        locinfo: loc_6 ;
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_26 ;
        LocInfoE loc_27 ("r") <-{ it_layout u32 }
          LocInfoE loc_28 ((LocInfoE loc_29 (use{it_layout u32} (LocInfoE loc_30 ("r")))) +{IntOp u32, IntOp u32} (LocInfoE loc_31 (use{it_layout u32} (LocInfoE loc_32 ("arg2"))))) ;
        locinfo: loc_17 ;
        Goto "#2"
      ]> $
      <[ "#7" :=
        locinfo: loc_17 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        locinfo: loc_43 ;
        LocInfoE loc_44 ("r") <-{ it_layout u32 }
          LocInfoE loc_45 ((LocInfoE loc_46 (use{it_layout u32} (LocInfoE loc_47 ("r")))) +{IntOp u32, IntOp u32} (LocInfoE loc_48 (use{it_layout u32} (LocInfoE loc_49 ("arg1"))))) ;
        locinfo: loc_34 ;
        Goto "#1"
      ]> $
      <[ "#9" :=
        locinfo: loc_34 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
