From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t01_basic.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_1 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_1 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_1 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_1 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_0 35 4 35 13.
  Definition loc_12 : location_info := LocationInfo file_0 35 11 35 12.
  Definition loc_13 : location_info := LocationInfo file_0 35 11 35 12.
  Definition loc_16 : location_info := LocationInfo file_0 128 4 128 13.
  Definition loc_17 : location_info := LocationInfo file_0 128 11 128 12.
  Definition loc_18 : location_info := LocationInfo file_0 128 11 128 12.
  Definition loc_21 : location_info := LocationInfo file_0 154 4 154 17.
  Definition loc_22 : location_info := LocationInfo file_0 154 11 154 16.
  Definition loc_23 : location_info := LocationInfo file_0 154 11 154 12.
  Definition loc_24 : location_info := LocationInfo file_0 154 11 154 12.
  Definition loc_25 : location_info := LocationInfo file_0 154 15 154 16.
  Definition loc_28 : location_info := LocationInfo file_0 256 4 260 5.
  Definition loc_29 : location_info := LocationInfo file_0 263 4 263 19.
  Definition loc_30 : location_info := LocationInfo file_0 264 4 264 19.
  Definition loc_31 : location_info := LocationInfo file_0 265 4 265 13.
  Definition loc_32 : location_info := LocationInfo file_0 265 11 265 12.
  Definition loc_33 : location_info := LocationInfo file_0 265 11 265 12.
  Definition loc_34 : location_info := LocationInfo file_0 264 11 264 17.
  Definition loc_35 : location_info := LocationInfo file_0 264 11 264 12.
  Definition loc_36 : location_info := LocationInfo file_0 264 11 264 12.
  Definition loc_37 : location_info := LocationInfo file_0 264 16 264 17.
  Definition loc_38 : location_info := LocationInfo file_0 264 16 264 17.
  Definition loc_39 : location_info := LocationInfo file_0 263 11 263 17.
  Definition loc_40 : location_info := LocationInfo file_0 263 11 263 12.
  Definition loc_41 : location_info := LocationInfo file_0 263 11 263 12.
  Definition loc_42 : location_info := LocationInfo file_0 263 16 263 17.
  Definition loc_43 : location_info := LocationInfo file_0 263 16 263 17.
  Definition loc_44 : location_info := LocationInfo file_0 256 14 258 5.
  Definition loc_45 : location_info := LocationInfo file_0 257 8 257 14.
  Definition loc_46 : location_info := LocationInfo file_0 257 8 257 9.
  Definition loc_47 : location_info := LocationInfo file_0 257 12 257 13.
  Definition loc_48 : location_info := LocationInfo file_0 257 12 257 13.
  Definition loc_49 : location_info := LocationInfo file_0 258 11 260 5.
  Definition loc_50 : location_info := LocationInfo file_0 259 8 259 14.
  Definition loc_51 : location_info := LocationInfo file_0 259 8 259 9.
  Definition loc_52 : location_info := LocationInfo file_0 259 12 259 13.
  Definition loc_53 : location_info := LocationInfo file_0 259 12 259 13.
  Definition loc_54 : location_info := LocationInfo file_0 256 7 256 12.
  Definition loc_55 : location_info := LocationInfo file_0 256 7 256 8.
  Definition loc_56 : location_info := LocationInfo file_0 256 7 256 8.
  Definition loc_57 : location_info := LocationInfo file_0 256 11 256 12.
  Definition loc_58 : location_info := LocationInfo file_0 256 11 256 12.
  Definition loc_61 : location_info := LocationInfo file_0 302 4 307 5.
  Definition loc_62 : location_info := LocationInfo file_0 308 4 308 13.
  Definition loc_63 : location_info := LocationInfo file_0 308 11 308 12.
  Definition loc_64 : location_info := LocationInfo file_0 308 11 308 12.
  Definition loc_65 : location_info := LocationInfo file_0 302 4 307 5.
  Definition loc_66 : location_info := LocationInfo file_0 302 17 307 5.
  Definition loc_67 : location_info := LocationInfo file_0 303 8 303 12.
  Definition loc_68 : location_info := LocationInfo file_0 306 8 306 12.
  Definition loc_69 : location_info := LocationInfo file_0 302 4 307 5.
  Definition loc_70 : location_info := LocationInfo file_0 302 4 307 5.
  Definition loc_71 : location_info := LocationInfo file_0 306 8 306 9.
  Definition loc_72 : location_info := LocationInfo file_0 303 8 303 9.
  Definition loc_73 : location_info := LocationInfo file_0 302 10 302 15.
  Definition loc_74 : location_info := LocationInfo file_0 302 10 302 11.
  Definition loc_75 : location_info := LocationInfo file_0 302 10 302 11.
  Definition loc_76 : location_info := LocationInfo file_0 302 14 302 15.
  Definition loc_79 : location_info := LocationInfo file_0 398 4 398 13.
  Definition loc_80 : location_info := LocationInfo file_0 398 4 398 8.
  Definition loc_81 : location_info := LocationInfo file_0 398 5 398 8.
  Definition loc_82 : location_info := LocationInfo file_0 398 5 398 8.
  Definition loc_83 : location_info := LocationInfo file_0 398 11 398 12.
  Definition loc_86 : location_info := LocationInfo file_0 409 2 409 15.
  Definition loc_87 : location_info := LocationInfo file_0 410 2 410 15.
  Definition loc_88 : location_info := LocationInfo file_0 410 2 410 10.
  Definition loc_89 : location_info := LocationInfo file_0 410 2 410 10.
  Definition loc_90 : location_info := LocationInfo file_0 410 11 410 13.
  Definition loc_91 : location_info := LocationInfo file_0 410 12 410 13.
  Definition loc_92 : location_info := LocationInfo file_0 409 2 409 10.
  Definition loc_93 : location_info := LocationInfo file_0 409 2 409 10.
  Definition loc_94 : location_info := LocationInfo file_0 409 11 409 13.
  Definition loc_95 : location_info := LocationInfo file_0 409 12 409 13.
  Definition loc_98 : location_info := LocationInfo file_0 430 4 430 34.
  Definition loc_99 : location_info := LocationInfo file_0 431 4 431 13.
  Definition loc_100 : location_info := LocationInfo file_0 431 4 431 10.
  Definition loc_101 : location_info := LocationInfo file_0 431 4 431 7.
  Definition loc_102 : location_info := LocationInfo file_0 431 4 431 7.
  Definition loc_103 : location_info := LocationInfo file_0 430 4 430 8.
  Definition loc_104 : location_info := LocationInfo file_0 430 5 430 8.
  Definition loc_105 : location_info := LocationInfo file_0 430 5 430 8.
  Definition loc_106 : location_info := LocationInfo file_0 430 11 430 33.
  Definition loc_107 : location_info := LocationInfo file_0 430 11 430 33.
  Definition loc_109 : location_info := LocationInfo file_0 430 31 430 32.

  (* Definition of struct [basic]. *)
  Program Definition struct_basic := {|
    sl_members := [
      (Some "a", it_layout i32);
      (Some "b", it_layout i32)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

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
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 (use{IntOp i32} (LocInfoE loc_13 ("a"))))
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
        locinfo: loc_16 ;
        Return (LocInfoE loc_17 (use{IntOp i32} (LocInfoE loc_18 ("a"))))
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
        locinfo: loc_21 ;
        Return (LocInfoE loc_22 ((LocInfoE loc_23 (use{IntOp i32} (LocInfoE loc_24 ("a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_25 (i2v 1 i32))))
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
        locinfo: loc_54 ;
        if: LocInfoE loc_54 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_54 ((LocInfoE loc_55 (use{IntOp i32} (LocInfoE loc_56 ("a")))) <{IntOp i32, IntOp i32} (LocInfoE loc_57 (use{IntOp i32} (LocInfoE loc_58 ("b")))))))
        then
        locinfo: loc_45 ;
          Goto "#2"
        else
        locinfo: loc_50 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_29 ;
        assert: (LocInfoE loc_39 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_39 ((LocInfoE loc_40 (use{IntOp i32} (LocInfoE loc_41 ("r")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_42 (use{IntOp i32} (LocInfoE loc_43 ("b")))))))) ;
        locinfo: loc_30 ;
        assert: (LocInfoE loc_34 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_34 ((LocInfoE loc_35 (use{IntOp i32} (LocInfoE loc_36 ("r")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_37 (use{IntOp i32} (LocInfoE loc_38 ("a")))))))) ;
        locinfo: loc_31 ;
        Return (LocInfoE loc_32 (use{IntOp i32} (LocInfoE loc_33 ("r"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_45 ;
        LocInfoE loc_46 ("r") <-{ IntOp i32 }
          LocInfoE loc_47 (use{IntOp i32} (LocInfoE loc_48 ("a"))) ;
        locinfo: loc_29 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_50 ;
        LocInfoE loc_51 ("r") <-{ IntOp i32 }
          LocInfoE loc_52 (use{IntOp i32} (LocInfoE loc_53 ("b"))) ;
        locinfo: loc_29 ;
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
        locinfo: loc_61 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_73 ;
        if: LocInfoE loc_73 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_73 ((LocInfoE loc_74 (use{IntOp i32} (LocInfoE loc_75 ("a")))) >{IntOp i32, IntOp i32} (LocInfoE loc_76 (i2v 0 i32)))))
        then
        locinfo: loc_67 ;
          Goto "#2"
        else
        locinfo: loc_62 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_67 ;
        LocInfoE loc_72 ("b") <-{ IntOp i32 }
          LocInfoE loc_67 ((LocInfoE loc_67 (use{IntOp i32} (LocInfoE loc_72 ("b")))) +{IntOp i32, IntOp i32} (LocInfoE loc_67 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        LocInfoE loc_71 ("a") <-{ IntOp i32 }
          LocInfoE loc_68 ((LocInfoE loc_68 (use{IntOp i32} (LocInfoE loc_71 ("a")))) -{IntOp i32, IntOp i32} (LocInfoE loc_68 (i2v 1 i32))) ;
        locinfo: loc_69 ;
        Goto "continue14"
      ]> $
      <[ "#3" :=
        locinfo: loc_62 ;
        Return (LocInfoE loc_63 (use{IntOp i32} (LocInfoE loc_64 ("b"))))
      ]> $
      <[ "continue14" :=
        locinfo: loc_61 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_int]. *)
  Definition impl_init_int : function := {|
    f_args := [
      ("out", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_79 ;
        LocInfoE loc_81 (!{PtrOp} (LocInfoE loc_82 ("out"))) <-{ IntOp i32 }
          LocInfoE loc_83 (i2v 1 i32) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_int_test]. *)
  Definition impl_init_int_test (global_init_int : loc): function := {|
    f_args := [
      ("out", void*)
    ];
    f_local_vars := [
      ("i", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_86 ;
        expr: (LocInfoE loc_86 (Call (LocInfoE loc_93 (global_init_int)) [@{expr} LocInfoE loc_94 (&(LocInfoE loc_95 ("i"))) ])) ;
        locinfo: loc_87 ;
        expr: (LocInfoE loc_87 (Call (LocInfoE loc_89 (global_init_int)) [@{expr} LocInfoE loc_90 (&(LocInfoE loc_91 ("i"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [struct_test]. *)
  Definition impl_struct_test : function := {|
    f_args := [
      ("out", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_98 ;
        LocInfoE loc_104 (!{PtrOp} (LocInfoE loc_105 ("out"))) <-{ StructOp struct_basic ([ IntOp i32 ; IntOp i32 ]) }
          StructInit struct_basic [
            ("a", LocInfoE loc_109 (i2v 1 i32) : expr) ;
            ("b", i2v 0 i32 : expr)
          ] ;
        locinfo: loc_99 ;
        LocInfoE loc_100 ((LocInfoE loc_101 (!{PtrOp} (LocInfoE loc_102 ("out")))) at{struct_basic} "a") <-{ IntOp i32 }
          LocInfoE loc_99 ((LocInfoE loc_99 (use{IntOp i32} (LocInfoE loc_100 ((LocInfoE loc_101 (!{PtrOp} (LocInfoE loc_102 ("out")))) at{struct_basic} "a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_99 (i2v 1 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
