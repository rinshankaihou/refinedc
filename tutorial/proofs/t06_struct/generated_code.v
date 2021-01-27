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
  Definition loc_6 : location_info := LocationInfo file_0 18 30 18 31.
  Definition loc_7 : location_info := LocationInfo file_0 18 30 18 31.
  Definition loc_8 : location_info := LocationInfo file_0 18 38 18 39.
  Definition loc_9 : location_info := LocationInfo file_0 18 38 18 39.
  Definition loc_10 : location_info := LocationInfo file_0 18 46 18 47.
  Definition loc_11 : location_info := LocationInfo file_0 18 46 18 47.
  Definition loc_14 : location_info := LocationInfo file_0 25 2 25 30.
  Definition loc_15 : location_info := LocationInfo file_0 26 2 26 11.
  Definition loc_16 : location_info := LocationInfo file_0 26 9 26 10.
  Definition loc_17 : location_info := LocationInfo file_0 26 9 26 10.
  Definition loc_19 : location_info := LocationInfo file_0 25 26 25 27.
  Definition loc_20 : location_info := LocationInfo file_0 25 26 25 27.
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
  Definition loc_47 : location_info := LocationInfo file_0 41 27 41 28.
  Definition loc_48 : location_info := LocationInfo file_0 41 27 41 28.
  Definition loc_51 : location_info := LocationInfo file_0 49 2 49 13.
  Definition loc_52 : location_info := LocationInfo file_0 49 9 49 12.
  Definition loc_53 : location_info := LocationInfo file_0 49 9 49 12.
  Definition loc_54 : location_info := LocationInfo file_0 49 9 49 10.
  Definition loc_57 : location_info := LocationInfo file_0 56 2 56 13.
  Definition loc_58 : location_info := LocationInfo file_0 56 2 56 8.
  Definition loc_59 : location_info := LocationInfo file_0 56 2 56 6.
  Definition loc_60 : location_info := LocationInfo file_0 56 4 56 5.
  Definition loc_61 : location_info := LocationInfo file_0 56 4 56 5.
  Definition loc_62 : location_info := LocationInfo file_0 56 11 56 12.
  Definition loc_63 : location_info := LocationInfo file_0 56 11 56 12.
  Definition loc_66 : location_info := LocationInfo file_0 63 2 63 13.
  Definition loc_67 : location_info := LocationInfo file_0 63 2 63 8.
  Definition loc_68 : location_info := LocationInfo file_0 63 2 63 6.
  Definition loc_69 : location_info := LocationInfo file_0 63 4 63 5.
  Definition loc_70 : location_info := LocationInfo file_0 63 4 63 5.
  Definition loc_71 : location_info := LocationInfo file_0 63 11 63 12.
  Definition loc_72 : location_info := LocationInfo file_0 63 11 63 12.
  Definition loc_75 : location_info := LocationInfo file_0 70 2 70 13.
  Definition loc_76 : location_info := LocationInfo file_0 70 2 70 8.
  Definition loc_77 : location_info := LocationInfo file_0 70 2 70 6.
  Definition loc_78 : location_info := LocationInfo file_0 70 4 70 5.
  Definition loc_79 : location_info := LocationInfo file_0 70 4 70 5.
  Definition loc_80 : location_info := LocationInfo file_0 70 11 70 12.
  Definition loc_81 : location_info := LocationInfo file_0 70 11 70 12.
  Definition loc_84 : location_info := LocationInfo file_0 75 2 75 41.
  Definition loc_85 : location_info := LocationInfo file_0 75 9 75 39.
  Definition loc_86 : location_info := LocationInfo file_0 75 9 75 25.
  Definition loc_87 : location_info := LocationInfo file_0 75 9 75 16.
  Definition loc_88 : location_info := LocationInfo file_0 75 9 75 16.
  Definition loc_89 : location_info := LocationInfo file_0 75 17 75 24.
  Definition loc_90 : location_info := LocationInfo file_0 75 17 75 21.
  Definition loc_91 : location_info := LocationInfo file_0 75 17 75 21.
  Definition loc_92 : location_info := LocationInfo file_0 75 22 75 23.
  Definition loc_93 : location_info := LocationInfo file_0 75 29 75 39.
  Definition loc_94 : location_info := LocationInfo file_0 75 38 75 39.

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
                  ("r", LocInfoE loc_6 (use{it_layout u8} (LocInfoE loc_7 ("r"))) : expr) ;
                  ("g", LocInfoE loc_8 (use{it_layout u8} (LocInfoE loc_9 ("g"))) : expr) ;
                  ("b", LocInfoE loc_10 (use{it_layout u8} (LocInfoE loc_11 ("b"))) : expr)
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
            ("r", LocInfoE loc_19 (use{it_layout u8} (LocInfoE loc_20 ("r"))) : expr) ;
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
            ("b", LocInfoE loc_47 (use{it_layout u8} (LocInfoE loc_48 ("b"))) : expr)
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

  (* Definition of function [set_red]. *)
  Definition impl_set_red : function := {|
    f_args := [
      ("c", void*);
      ("r", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_57 ;
        LocInfoE loc_58 ((LocInfoE loc_60 (!{void*} (LocInfoE loc_61 ("c")))) at{struct_color} "r") <-{ it_layout u8 }
          LocInfoE loc_62 (use{it_layout u8} (LocInfoE loc_63 ("r"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [set_green]. *)
  Definition impl_set_green : function := {|
    f_args := [
      ("c", void*);
      ("g", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_66 ;
        LocInfoE loc_67 ((LocInfoE loc_69 (!{void*} (LocInfoE loc_70 ("c")))) at{struct_color} "g") <-{ it_layout u8 }
          LocInfoE loc_71 (use{it_layout u8} (LocInfoE loc_72 ("g"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [set_blue]. *)
  Definition impl_set_blue : function := {|
    f_args := [
      ("c", void*);
      ("b", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_75 ;
        LocInfoE loc_76 ((LocInfoE loc_78 (!{void*} (LocInfoE loc_79 ("c")))) at{struct_color} "b") <-{ it_layout u8 }
          LocInfoE loc_80 (use{it_layout u8} (LocInfoE loc_81 ("b"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [argtest]. *)
  Definition impl_argtest (global_blue global_getblue : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_84 ;
        assert: (LocInfoE loc_85 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_85 ((LocInfoE loc_86 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_86 (Call (LocInfoE loc_88 (global_getblue)) [@{expr} LocInfoE loc_89 (Call (LocInfoE loc_91 (global_blue)) [@{expr} LocInfoE loc_92 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_92 (i2v 5 i32))) ]) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_93 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_93 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_94 (i2v 5 i32)))))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
