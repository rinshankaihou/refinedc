From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t06_struct.c".
  Definition loc_2 : location_info := LocationInfo file_0 18 2 18 50.
  Definition loc_3 : location_info := LocationInfo file_0 18 9 18 49.
  Definition loc_4 : location_info := LocationInfo file_0 18 9 18 49.
  Definition loc_6 : location_info := LocationInfo file_0 18 46 18 47.
  Definition loc_7 : location_info := LocationInfo file_0 18 46 18 47.
  Definition loc_8 : location_info := LocationInfo file_0 18 38 18 39.
  Definition loc_9 : location_info := LocationInfo file_0 18 38 18 39.
  Definition loc_10 : location_info := LocationInfo file_0 18 30 18 31.
  Definition loc_11 : location_info := LocationInfo file_0 18 30 18 31.
  Definition loc_14 : location_info := LocationInfo file_0 25 2 25 30.
  Definition loc_15 : location_info := LocationInfo file_0 26 2 26 11.
  Definition loc_16 : location_info := LocationInfo file_0 26 9 26 10.
  Definition loc_17 : location_info := LocationInfo file_0 26 9 26 10.
  Definition loc_21 : location_info := LocationInfo file_0 25 26 25 27.
  Definition loc_22 : location_info := LocationInfo file_0 25 26 25 27.
  Definition loc_27 : location_info := LocationInfo file_0 33 2 33 35.
  Definition loc_28 : location_info := LocationInfo file_0 33 9 33 34.
  Definition loc_29 : location_info := LocationInfo file_0 33 9 33 34.
  Definition loc_32 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_33 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_37 : location_info := LocationInfo file_0 41 2 41 31.
  Definition loc_38 : location_info := LocationInfo file_0 42 2 42 11.
  Definition loc_39 : location_info := LocationInfo file_0 42 9 42 10.
  Definition loc_40 : location_info := LocationInfo file_0 42 9 42 10.
  Definition loc_41 : location_info := LocationInfo file_0 41 2 41 3.
  Definition loc_42 : location_info := LocationInfo file_0 41 6 41 30.
  Definition loc_43 : location_info := LocationInfo file_0 41 6 41 30.
  Definition loc_45 : location_info := LocationInfo file_0 41 27 41 28.
  Definition loc_46 : location_info := LocationInfo file_0 41 27 41 28.
  Definition loc_51 : location_info := LocationInfo file_0 49 2 49 13.
  Definition loc_52 : location_info := LocationInfo file_0 49 9 49 12.
  Definition loc_53 : location_info := LocationInfo file_0 49 9 49 12.
  Definition loc_54 : location_info := LocationInfo file_0 49 9 49 10.
  Definition loc_57 : location_info := LocationInfo file_0 54 2 54 41.
  Definition loc_58 : location_info := LocationInfo file_0 54 9 54 39.
  Definition loc_59 : location_info := LocationInfo file_0 54 9 54 25.
  Definition loc_60 : location_info := LocationInfo file_0 54 9 54 16.
  Definition loc_61 : location_info := LocationInfo file_0 54 9 54 16.
  Definition loc_62 : location_info := LocationInfo file_0 54 17 54 24.
  Definition loc_63 : location_info := LocationInfo file_0 54 17 54 21.
  Definition loc_64 : location_info := LocationInfo file_0 54 17 54 21.
  Definition loc_65 : location_info := LocationInfo file_0 54 22 54 23.
  Definition loc_66 : location_info := LocationInfo file_0 54 29 54 39.
  Definition loc_67 : location_info := LocationInfo file_0 54 38 54 39.

  (* Definition of struct [color]. *)
  Program Definition struct_color := {|
    sl_members := [
      (Some "r", it_layout u8);
      (Some "g", it_layout u8);
      (Some "b", it_layout u8)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [rgb]. *)
  Definition impl_rgb : function := {|
    f_args := [
      ("r", it_layout u8);
      ("g", it_layout u8);
      ("b", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (StructInit struct_color [
                  ("r", LocInfoE loc_10 (use{it_layout u8} (LocInfoE loc_11 ("r"))) : expr) ;
                  ("g", LocInfoE loc_8 (use{it_layout u8} (LocInfoE loc_9 ("g"))) : expr) ;
                  ("b", LocInfoE loc_6 (use{it_layout u8} (LocInfoE loc_7 ("b"))) : expr)
                ])
      ]> $∅
    )%E
  |}.

  (* Definition of function [red]. *)
  Definition impl_red : function := {|
    f_args := [
      ("r", it_layout u8)
    ];
    f_local_vars := [
      ("c", layout_of struct_color)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "c" <-{ layout_of struct_color }
          StructInit struct_color [
            ("r", LocInfoE loc_21 (use{it_layout u8} (LocInfoE loc_22 ("r"))) : expr) ;
            ("g", UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) : expr) ;
            ("b", UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) : expr)
          ] ;
        locinfo: loc_15 ;
        Return (LocInfoE loc_16 (use{layout_of struct_color} (LocInfoE loc_17 ("c"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [green]. *)
  Definition impl_green : function := {|
    f_args := [
      ("g", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_27 ;
        Return (StructInit struct_color [
                  ("r", UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) : expr) ;
                  ("g", LocInfoE loc_32 (use{it_layout u8} (LocInfoE loc_33 ("g"))) : expr) ;
                  ("b", UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) : expr)
                ])
      ]> $∅
    )%E
  |}.

  (* Definition of function [blue]. *)
  Definition impl_blue : function := {|
    f_args := [
      ("b", it_layout u8)
    ];
    f_local_vars := [
      ("c", layout_of struct_color)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_37 ;
        LocInfoE loc_41 ("c") <-{ layout_of struct_color }
          StructInit struct_color [
            ("r", UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) : expr) ;
            ("g", UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) : expr) ;
            ("b", LocInfoE loc_45 (use{it_layout u8} (LocInfoE loc_46 ("b"))) : expr)
          ] ;
        locinfo: loc_38 ;
        Return (LocInfoE loc_39 (use{layout_of struct_color} (LocInfoE loc_40 ("c"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [getblue]. *)
  Definition impl_getblue : function := {|
    f_args := [
      ("b", layout_of struct_color)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_51 ;
        Return (LocInfoE loc_52 (use{it_layout u8} (LocInfoE loc_53 ((LocInfoE loc_54 ("b")) at{struct_color} "b"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [argtest]. *)
  Definition impl_argtest (blue getblue : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_62 ;
        "$0" <- LocInfoE loc_64 (blue) with
          [ LocInfoE loc_65 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_65 (i2v 5 i32))) ] ;
        locinfo: loc_59 ;
        "$1" <- LocInfoE loc_61 (getblue) with [ LocInfoE loc_62 ("$0") ] ;
        locinfo: loc_57 ;
        assert: (LocInfoE loc_58 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_58 ((LocInfoE loc_59 ("$1")) ={IntOp u8, IntOp u8} (LocInfoE loc_66 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_67 (i2v 5 i32)))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
