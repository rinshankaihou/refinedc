From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t01_basic.c".
  Definition loc_2 : location_info := LocationInfo file_0 35 4 35 13.
  Definition loc_3 : location_info := LocationInfo file_0 35 11 35 12.
  Definition loc_4 : location_info := LocationInfo file_0 35 11 35 12.
  Definition loc_7 : location_info := LocationInfo file_0 128 4 128 13.
  Definition loc_8 : location_info := LocationInfo file_0 128 11 128 12.
  Definition loc_9 : location_info := LocationInfo file_0 128 11 128 12.
  Definition loc_12 : location_info := LocationInfo file_0 154 4 154 17.
  Definition loc_13 : location_info := LocationInfo file_0 154 11 154 16.
  Definition loc_14 : location_info := LocationInfo file_0 154 11 154 12.
  Definition loc_15 : location_info := LocationInfo file_0 154 11 154 12.
  Definition loc_16 : location_info := LocationInfo file_0 154 15 154 16.
  Definition loc_19 : location_info := LocationInfo file_0 260 4 264 5.
  Definition loc_20 : location_info := LocationInfo file_0 267 4 267 19.
  Definition loc_21 : location_info := LocationInfo file_0 268 4 268 19.
  Definition loc_22 : location_info := LocationInfo file_0 269 4 269 13.
  Definition loc_23 : location_info := LocationInfo file_0 269 11 269 12.
  Definition loc_24 : location_info := LocationInfo file_0 269 11 269 12.
  Definition loc_25 : location_info := LocationInfo file_0 268 11 268 17.
  Definition loc_26 : location_info := LocationInfo file_0 268 11 268 12.
  Definition loc_27 : location_info := LocationInfo file_0 268 11 268 12.
  Definition loc_28 : location_info := LocationInfo file_0 268 16 268 17.
  Definition loc_29 : location_info := LocationInfo file_0 268 16 268 17.
  Definition loc_30 : location_info := LocationInfo file_0 267 11 267 17.
  Definition loc_31 : location_info := LocationInfo file_0 267 11 267 12.
  Definition loc_32 : location_info := LocationInfo file_0 267 11 267 12.
  Definition loc_33 : location_info := LocationInfo file_0 267 16 267 17.
  Definition loc_34 : location_info := LocationInfo file_0 267 16 267 17.
  Definition loc_35 : location_info := LocationInfo file_0 260 14 262 5.
  Definition loc_36 : location_info := LocationInfo file_0 261 8 261 14.
  Definition loc_37 : location_info := LocationInfo file_0 261 8 261 9.
  Definition loc_38 : location_info := LocationInfo file_0 261 12 261 13.
  Definition loc_39 : location_info := LocationInfo file_0 261 12 261 13.
  Definition loc_40 : location_info := LocationInfo file_0 262 11 264 5.
  Definition loc_41 : location_info := LocationInfo file_0 263 8 263 14.
  Definition loc_42 : location_info := LocationInfo file_0 263 8 263 9.
  Definition loc_43 : location_info := LocationInfo file_0 263 12 263 13.
  Definition loc_44 : location_info := LocationInfo file_0 263 12 263 13.
  Definition loc_45 : location_info := LocationInfo file_0 260 7 260 12.
  Definition loc_46 : location_info := LocationInfo file_0 260 7 260 8.
  Definition loc_47 : location_info := LocationInfo file_0 260 7 260 8.
  Definition loc_48 : location_info := LocationInfo file_0 260 11 260 12.
  Definition loc_49 : location_info := LocationInfo file_0 260 11 260 12.
  Definition loc_52 : location_info := LocationInfo file_0 306 4 311 5.
  Definition loc_53 : location_info := LocationInfo file_0 312 4 312 13.
  Definition loc_54 : location_info := LocationInfo file_0 312 11 312 12.
  Definition loc_55 : location_info := LocationInfo file_0 312 11 312 12.
  Definition loc_56 : location_info := LocationInfo file_0 306 4 311 5.
  Definition loc_57 : location_info := LocationInfo file_0 306 17 311 5.
  Definition loc_58 : location_info := LocationInfo file_0 307 8 307 12.
  Definition loc_59 : location_info := LocationInfo file_0 310 8 310 12.
  Definition loc_60 : location_info := LocationInfo file_0 306 4 311 5.
  Definition loc_61 : location_info := LocationInfo file_0 306 4 311 5.
  Definition loc_62 : location_info := LocationInfo file_0 310 8 310 9.
  Definition loc_63 : location_info := LocationInfo file_0 307 8 307 9.
  Definition loc_64 : location_info := LocationInfo file_0 306 10 306 15.
  Definition loc_65 : location_info := LocationInfo file_0 306 10 306 11.
  Definition loc_66 : location_info := LocationInfo file_0 306 10 306 11.
  Definition loc_67 : location_info := LocationInfo file_0 306 14 306 15.
  Definition loc_70 : location_info := LocationInfo file_0 402 4 402 13.
  Definition loc_71 : location_info := LocationInfo file_0 402 4 402 8.
  Definition loc_72 : location_info := LocationInfo file_0 402 5 402 8.
  Definition loc_73 : location_info := LocationInfo file_0 402 5 402 8.
  Definition loc_74 : location_info := LocationInfo file_0 402 11 402 12.
  Definition loc_77 : location_info := LocationInfo file_0 413 2 413 15.
  Definition loc_78 : location_info := LocationInfo file_0 414 2 414 15.
  Definition loc_79 : location_info := LocationInfo file_0 414 2 414 10.
  Definition loc_80 : location_info := LocationInfo file_0 414 2 414 10.
  Definition loc_81 : location_info := LocationInfo file_0 414 11 414 13.
  Definition loc_82 : location_info := LocationInfo file_0 414 12 414 13.
  Definition loc_83 : location_info := LocationInfo file_0 413 2 413 10.
  Definition loc_84 : location_info := LocationInfo file_0 413 2 413 10.
  Definition loc_85 : location_info := LocationInfo file_0 413 11 413 13.
  Definition loc_86 : location_info := LocationInfo file_0 413 12 413 13.
  Definition loc_89 : location_info := LocationInfo file_0 434 4 434 34.
  Definition loc_90 : location_info := LocationInfo file_0 435 4 435 13.
  Definition loc_91 : location_info := LocationInfo file_0 435 4 435 10.
  Definition loc_92 : location_info := LocationInfo file_0 435 4 435 7.
  Definition loc_93 : location_info := LocationInfo file_0 435 4 435 7.
  Definition loc_94 : location_info := LocationInfo file_0 434 4 434 8.
  Definition loc_95 : location_info := LocationInfo file_0 434 5 434 8.
  Definition loc_96 : location_info := LocationInfo file_0 434 5 434 8.
  Definition loc_97 : location_info := LocationInfo file_0 434 11 434 33.
  Definition loc_98 : location_info := LocationInfo file_0 434 11 434 33.
  Definition loc_101 : location_info := LocationInfo file_0 434 31 434 32.

  (* Definition of struct [basic]. *)
  Program Definition struct_basic := {|
    sl_members := [
      (Some "a", it_layout i32);
      (Some "b", it_layout i32)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [int_id]. *)
  Definition impl_int_id : function := {|
    f_args := [
      ("a", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (use{it_layout i32} (LocInfoE loc_4 ("a"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_id2]. *)
  Definition impl_int_id2 : function := {|
    f_args := [
      ("a", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_7 ;
        Return (LocInfoE loc_8 (use{it_layout i32} (LocInfoE loc_9 ("a"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [add1]. *)
  Definition impl_add1 : function := {|
    f_args := [
      ("a", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 ((LocInfoE loc_14 (use{it_layout i32} (LocInfoE loc_15 ("a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_16 (i2v 1 i32))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [min]. *)
  Definition impl_min : function := {|
    f_args := [
      ("a", it_layout i32);
      ("b", it_layout i32)
    ];
    f_local_vars := [
      ("r", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_45 ;
        if: LocInfoE loc_45 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_45 ((LocInfoE loc_46 (use{it_layout i32} (LocInfoE loc_47 ("a")))) <{IntOp i32, IntOp i32} (LocInfoE loc_48 (use{it_layout i32} (LocInfoE loc_49 ("b")))))))
        then
        locinfo: loc_36 ;
          Goto "#2"
        else
        locinfo: loc_41 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_20 ;
        assert: (LocInfoE loc_30 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_30 ((LocInfoE loc_31 (use{it_layout i32} (LocInfoE loc_32 ("r")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_33 (use{it_layout i32} (LocInfoE loc_34 ("b")))))))) ;
        locinfo: loc_21 ;
        assert: (LocInfoE loc_25 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_25 ((LocInfoE loc_26 (use{it_layout i32} (LocInfoE loc_27 ("r")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_28 (use{it_layout i32} (LocInfoE loc_29 ("a")))))))) ;
        locinfo: loc_22 ;
        Return (LocInfoE loc_23 (use{it_layout i32} (LocInfoE loc_24 ("r"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_36 ;
        LocInfoE loc_37 ("r") <-{ it_layout i32 }
          LocInfoE loc_38 (use{it_layout i32} (LocInfoE loc_39 ("a"))) ;
        locinfo: loc_20 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_41 ;
        LocInfoE loc_42 ("r") <-{ it_layout i32 }
          LocInfoE loc_43 (use{it_layout i32} (LocInfoE loc_44 ("b"))) ;
        locinfo: loc_20 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [looping_add]. *)
  Definition impl_looping_add : function := {|
    f_args := [
      ("a", it_layout i32);
      ("b", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_52 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_64 ;
        if: LocInfoE loc_64 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_64 ((LocInfoE loc_65 (use{it_layout i32} (LocInfoE loc_66 ("a")))) >{IntOp i32, IntOp i32} (LocInfoE loc_67 (i2v 0 i32)))))
        then
        locinfo: loc_58 ;
          Goto "#2"
        else
        locinfo: loc_53 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_58 ;
        LocInfoE loc_63 ("b") <-{ it_layout i32 }
          LocInfoE loc_58 ((LocInfoE loc_58 (use{it_layout i32} (LocInfoE loc_63 ("b")))) +{IntOp i32, IntOp i32} (LocInfoE loc_58 (i2v 1 i32))) ;
        locinfo: loc_59 ;
        LocInfoE loc_62 ("a") <-{ it_layout i32 }
          LocInfoE loc_59 ((LocInfoE loc_59 (use{it_layout i32} (LocInfoE loc_62 ("a")))) -{IntOp i32, IntOp i32} (LocInfoE loc_59 (i2v 1 i32))) ;
        locinfo: loc_60 ;
        Goto "continue12"
      ]> $
      <[ "#3" :=
        locinfo: loc_53 ;
        Return (LocInfoE loc_54 (use{it_layout i32} (LocInfoE loc_55 ("b"))))
      ]> $
      <[ "continue12" :=
        locinfo: loc_52 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_int]. *)
  Definition impl_init_int : function := {|
    f_args := [
      ("out", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_70 ;
        LocInfoE loc_72 (!{LPtr} (LocInfoE loc_73 ("out"))) <-{ it_layout i32 }
          LocInfoE loc_74 (i2v 1 i32) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_int_test]. *)
  Definition impl_init_int_test (init_int : loc): function := {|
    f_args := [
      ("out", LPtr)
    ];
    f_local_vars := [
      ("i", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_77 ;
        "_" <- LocInfoE loc_84 (init_int) with
          [ LocInfoE loc_85 (&(LocInfoE loc_86 ("i"))) ] ;
        locinfo: loc_78 ;
        "_" <- LocInfoE loc_80 (init_int) with
          [ LocInfoE loc_81 (&(LocInfoE loc_82 ("i"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [struct_test]. *)
  Definition impl_struct_test : function := {|
    f_args := [
      ("out", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_89 ;
        LocInfoE loc_95 (!{LPtr} (LocInfoE loc_96 ("out"))) <-{ layout_of struct_basic }
          StructInit struct_basic [
            ("a", LocInfoE loc_101 (i2v 1 i32) : expr) ;
            ("b", i2v 0 i32 : expr)
          ] ;
        locinfo: loc_90 ;
        LocInfoE loc_91 ((LocInfoE loc_92 (!{LPtr} (LocInfoE loc_93 ("out")))) at{struct_basic} "a") <-{ it_layout i32 }
          LocInfoE loc_90 ((LocInfoE loc_90 (use{it_layout i32} (LocInfoE loc_91 ((LocInfoE loc_92 (!{LPtr} (LocInfoE loc_93 ("out")))) at{struct_basic} "a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_90 (i2v 1 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
