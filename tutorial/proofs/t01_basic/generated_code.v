From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t01_basic.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_1 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_1 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 42 4 42 13.
  Definition loc_12 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_13 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_16 : location_info := LocationInfo file_0 145 4 145 13.
  Definition loc_17 : location_info := LocationInfo file_0 145 11 145 12.
  Definition loc_18 : location_info := LocationInfo file_0 145 11 145 12.
  Definition loc_21 : location_info := LocationInfo file_0 171 4 171 17.
  Definition loc_22 : location_info := LocationInfo file_0 171 11 171 16.
  Definition loc_23 : location_info := LocationInfo file_0 171 11 171 12.
  Definition loc_24 : location_info := LocationInfo file_0 171 11 171 12.
  Definition loc_25 : location_info := LocationInfo file_0 171 15 171 16.
  Definition loc_28 : location_info := LocationInfo file_0 277 4 277 10.
  Definition loc_29 : location_info := LocationInfo file_0 278 4 282 5.
  Definition loc_30 : location_info := LocationInfo file_0 285 4 285 19.
  Definition loc_31 : location_info := LocationInfo file_0 286 4 286 19.
  Definition loc_32 : location_info := LocationInfo file_0 287 4 287 13.
  Definition loc_33 : location_info := LocationInfo file_0 287 11 287 12.
  Definition loc_34 : location_info := LocationInfo file_0 287 11 287 12.
  Definition loc_35 : location_info := LocationInfo file_0 286 11 286 17.
  Definition loc_36 : location_info := LocationInfo file_0 286 11 286 12.
  Definition loc_37 : location_info := LocationInfo file_0 286 11 286 12.
  Definition loc_38 : location_info := LocationInfo file_0 286 16 286 17.
  Definition loc_39 : location_info := LocationInfo file_0 286 16 286 17.
  Definition loc_40 : location_info := LocationInfo file_0 285 11 285 17.
  Definition loc_41 : location_info := LocationInfo file_0 285 11 285 12.
  Definition loc_42 : location_info := LocationInfo file_0 285 11 285 12.
  Definition loc_43 : location_info := LocationInfo file_0 285 16 285 17.
  Definition loc_44 : location_info := LocationInfo file_0 285 16 285 17.
  Definition loc_45 : location_info := LocationInfo file_0 278 14 280 5.
  Definition loc_46 : location_info := LocationInfo file_0 279 8 279 14.
  Definition loc_47 : location_info := LocationInfo file_0 279 8 279 9.
  Definition loc_48 : location_info := LocationInfo file_0 279 12 279 13.
  Definition loc_49 : location_info := LocationInfo file_0 279 12 279 13.
  Definition loc_50 : location_info := LocationInfo file_0 280 11 282 5.
  Definition loc_51 : location_info := LocationInfo file_0 281 8 281 14.
  Definition loc_52 : location_info := LocationInfo file_0 281 8 281 9.
  Definition loc_53 : location_info := LocationInfo file_0 281 12 281 13.
  Definition loc_54 : location_info := LocationInfo file_0 281 12 281 13.
  Definition loc_55 : location_info := LocationInfo file_0 278 7 278 12.
  Definition loc_56 : location_info := LocationInfo file_0 278 7 278 8.
  Definition loc_57 : location_info := LocationInfo file_0 278 7 278 8.
  Definition loc_58 : location_info := LocationInfo file_0 278 11 278 12.
  Definition loc_59 : location_info := LocationInfo file_0 278 11 278 12.
  Definition loc_62 : location_info := LocationInfo file_0 334 4 339 5.
  Definition loc_63 : location_info := LocationInfo file_0 340 4 340 13.
  Definition loc_64 : location_info := LocationInfo file_0 340 11 340 12.
  Definition loc_65 : location_info := LocationInfo file_0 340 11 340 12.
  Definition loc_66 : location_info := LocationInfo file_0 334 17 339 5.
  Definition loc_67 : location_info := LocationInfo file_0 335 8 335 12.
  Definition loc_68 : location_info := LocationInfo file_0 338 8 338 12.
  Definition loc_69 : location_info := LocationInfo file_0 338 8 338 9.
  Definition loc_70 : location_info := LocationInfo file_0 335 8 335 9.
  Definition loc_71 : location_info := LocationInfo file_0 334 10 334 15.
  Definition loc_72 : location_info := LocationInfo file_0 334 10 334 11.
  Definition loc_73 : location_info := LocationInfo file_0 334 10 334 11.
  Definition loc_74 : location_info := LocationInfo file_0 334 14 334 15.
  Definition loc_77 : location_info := LocationInfo file_0 433 2 433 10.
  Definition loc_78 : location_info := LocationInfo file_0 435 2 435 19.
  Definition loc_79 : location_info := LocationInfo file_0 437 2 437 10.
  Definition loc_80 : location_info := LocationInfo file_0 439 2 439 19.
  Definition loc_81 : location_info := LocationInfo file_0 440 2 440 19.
  Definition loc_82 : location_info := LocationInfo file_0 440 9 440 17.
  Definition loc_83 : location_info := LocationInfo file_0 440 9 440 12.
  Definition loc_84 : location_info := LocationInfo file_0 440 9 440 12.
  Definition loc_85 : location_info := LocationInfo file_0 440 10 440 12.
  Definition loc_86 : location_info := LocationInfo file_0 440 10 440 12.
  Definition loc_87 : location_info := LocationInfo file_0 440 16 440 17.
  Definition loc_88 : location_info := LocationInfo file_0 439 9 439 17.
  Definition loc_89 : location_info := LocationInfo file_0 439 9 439 12.
  Definition loc_90 : location_info := LocationInfo file_0 439 9 439 12.
  Definition loc_91 : location_info := LocationInfo file_0 439 10 439 12.
  Definition loc_92 : location_info := LocationInfo file_0 439 10 439 12.
  Definition loc_93 : location_info := LocationInfo file_0 439 16 439 17.
  Definition loc_94 : location_info := LocationInfo file_0 437 2 437 5.
  Definition loc_95 : location_info := LocationInfo file_0 437 3 437 5.
  Definition loc_96 : location_info := LocationInfo file_0 437 3 437 5.
  Definition loc_97 : location_info := LocationInfo file_0 437 8 437 9.
  Definition loc_98 : location_info := LocationInfo file_0 435 9 435 17.
  Definition loc_99 : location_info := LocationInfo file_0 435 9 435 12.
  Definition loc_100 : location_info := LocationInfo file_0 435 9 435 12.
  Definition loc_101 : location_info := LocationInfo file_0 435 10 435 12.
  Definition loc_102 : location_info := LocationInfo file_0 435 10 435 12.
  Definition loc_103 : location_info := LocationInfo file_0 435 16 435 17.
  Definition loc_104 : location_info := LocationInfo file_0 433 2 433 5.
  Definition loc_105 : location_info := LocationInfo file_0 433 3 433 5.
  Definition loc_106 : location_info := LocationInfo file_0 433 3 433 5.
  Definition loc_107 : location_info := LocationInfo file_0 433 8 433 9.
  Definition loc_110 : location_info := LocationInfo file_0 474 2 474 21.
  Definition loc_111 : location_info := LocationInfo file_0 476 2 476 21.
  Definition loc_112 : location_info := LocationInfo file_0 476 2 476 10.
  Definition loc_113 : location_info := LocationInfo file_0 476 2 476 10.
  Definition loc_114 : location_info := LocationInfo file_0 476 11 476 14.
  Definition loc_115 : location_info := LocationInfo file_0 476 12 476 14.
  Definition loc_116 : location_info := LocationInfo file_0 476 16 476 19.
  Definition loc_117 : location_info := LocationInfo file_0 476 17 476 19.
  Definition loc_118 : location_info := LocationInfo file_0 474 19 474 20.
  Definition loc_121 : location_info := LocationInfo file_0 474 11 474 12.
  Definition loc_126 : location_info := LocationInfo file_0 567 4 567 13.
  Definition loc_127 : location_info := LocationInfo file_0 567 4 567 8.
  Definition loc_128 : location_info := LocationInfo file_0 567 5 567 8.
  Definition loc_129 : location_info := LocationInfo file_0 567 5 567 8.
  Definition loc_130 : location_info := LocationInfo file_0 567 11 567 12.
  Definition loc_133 : location_info := LocationInfo file_0 577 2 577 8.
  Definition loc_134 : location_info := LocationInfo file_0 578 2 578 15.
  Definition loc_135 : location_info := LocationInfo file_0 579 2 579 15.
  Definition loc_136 : location_info := LocationInfo file_0 579 2 579 10.
  Definition loc_137 : location_info := LocationInfo file_0 579 2 579 10.
  Definition loc_138 : location_info := LocationInfo file_0 579 11 579 13.
  Definition loc_139 : location_info := LocationInfo file_0 579 12 579 13.
  Definition loc_140 : location_info := LocationInfo file_0 578 2 578 10.
  Definition loc_141 : location_info := LocationInfo file_0 578 2 578 10.
  Definition loc_142 : location_info := LocationInfo file_0 578 11 578 13.
  Definition loc_143 : location_info := LocationInfo file_0 578 12 578 13.
  Definition loc_146 : location_info := LocationInfo file_0 599 4 599 34.
  Definition loc_147 : location_info := LocationInfo file_0 600 4 600 13.
  Definition loc_148 : location_info := LocationInfo file_0 600 4 600 10.
  Definition loc_149 : location_info := LocationInfo file_0 600 4 600 7.
  Definition loc_150 : location_info := LocationInfo file_0 600 4 600 7.
  Definition loc_151 : location_info := LocationInfo file_0 599 4 599 8.
  Definition loc_152 : location_info := LocationInfo file_0 599 5 599 8.
  Definition loc_153 : location_info := LocationInfo file_0 599 5 599 8.
  Definition loc_154 : location_info := LocationInfo file_0 599 11 599 33.
  Definition loc_155 : location_info := LocationInfo file_0 599 11 599 33.
  Definition loc_157 : location_info := LocationInfo file_0 599 31 599 32.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

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
        locinfo: loc_55 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_55 ((LocInfoE loc_56 (use{IntOp i32} (LocInfoE loc_57 ("a")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_58 (use{IntOp i32} (LocInfoE loc_59 ("b")))))
        then
        locinfo: loc_46 ;
          Goto "#2"
        else
        locinfo: loc_51 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_30 ;
        assert{IntOp i32}: (LocInfoE loc_40 ((LocInfoE loc_41 (use{IntOp i32} (LocInfoE loc_42 ("r")))) ≤{IntOp i32, IntOp i32, i32} (LocInfoE loc_43 (use{IntOp i32} (LocInfoE loc_44 ("a")))))) ;
        locinfo: loc_31 ;
        assert{IntOp i32}: (LocInfoE loc_35 ((LocInfoE loc_36 (use{IntOp i32} (LocInfoE loc_37 ("r")))) ≤{IntOp i32, IntOp i32, i32} (LocInfoE loc_38 (use{IntOp i32} (LocInfoE loc_39 ("b")))))) ;
        locinfo: loc_32 ;
        Return (LocInfoE loc_33 (use{IntOp i32} (LocInfoE loc_34 ("r"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_46 ;
        LocInfoE loc_47 ("r") <-{ IntOp i32 }
          LocInfoE loc_48 (use{IntOp i32} (LocInfoE loc_49 ("a"))) ;
        locinfo: loc_30 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_51 ;
        LocInfoE loc_52 ("r") <-{ IntOp i32 }
          LocInfoE loc_53 (use{IntOp i32} (LocInfoE loc_54 ("b"))) ;
        locinfo: loc_30 ;
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
        locinfo: loc_62 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_71 ;
        if{IntOp i32, None}: LocInfoE loc_71 ((LocInfoE loc_72 (use{IntOp i32} (LocInfoE loc_73 ("a")))) >{IntOp i32, IntOp i32, i32} (LocInfoE loc_74 (i2v 0 i32)))
        then
        locinfo: loc_67 ;
          Goto "#2"
        else
        locinfo: loc_63 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_67 ;
        LocInfoE loc_70 ("b") <-{ IntOp i32 }
          LocInfoE loc_67 ((LocInfoE loc_67 (use{IntOp i32} (LocInfoE loc_70 ("b")))) +{IntOp i32, IntOp i32} (LocInfoE loc_67 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        LocInfoE loc_69 ("a") <-{ IntOp i32 }
          LocInfoE loc_68 ((LocInfoE loc_68 (use{IntOp i32} (LocInfoE loc_69 ("a")))) -{IntOp i32, IntOp i32} (LocInfoE loc_68 (i2v 1 i32))) ;
        locinfo: loc_62 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_63 ;
        Return (LocInfoE loc_64 (use{IntOp i32} (LocInfoE loc_65 ("b"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_ptrs]. *)
  Definition impl_int_ptrs : function := {|
    f_args := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_77 ;
        LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("p1"))) <-{ IntOp i32 }
          LocInfoE loc_107 (i2v 1 i32) ;
        locinfo: loc_78 ;
        assert{IntOp i32}: (LocInfoE loc_98 ((LocInfoE loc_99 (use{IntOp i32} (LocInfoE loc_101 (!{PtrOp} (LocInfoE loc_102 ("p1")))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_103 (i2v 1 i32)))) ;
        locinfo: loc_79 ;
        LocInfoE loc_95 (!{PtrOp} (LocInfoE loc_96 ("p2"))) <-{ IntOp i32 }
          LocInfoE loc_97 (i2v 2 i32) ;
        locinfo: loc_80 ;
        assert{IntOp i32}: (LocInfoE loc_88 ((LocInfoE loc_89 (use{IntOp i32} (LocInfoE loc_91 (!{PtrOp} (LocInfoE loc_92 ("p1")))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_93 (i2v 1 i32)))) ;
        locinfo: loc_81 ;
        assert{IntOp i32}: (LocInfoE loc_82 ((LocInfoE loc_83 (use{IntOp i32} (LocInfoE loc_85 (!{PtrOp} (LocInfoE loc_86 ("p2")))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_87 (i2v 2 i32)))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [call_int_ptrs]. *)
  Definition impl_call_int_ptrs (global_int_ptrs : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("p1", it_layout i32);
      ("p2", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p1" <-{ IntOp i32 } LocInfoE loc_121 (i2v 0 i32) ;
        "p2" <-{ IntOp i32 } LocInfoE loc_118 (i2v 0 i32) ;
        locinfo: loc_111 ;
        expr: (LocInfoE loc_111 (Call (LocInfoE loc_113 (global_int_ptrs)) [@{expr} LocInfoE loc_114 (&(LocInfoE loc_115 ("p1"))) ;
        LocInfoE loc_116 (&(LocInfoE loc_117 ("p2"))) ])) ;
        Return (VOID)
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
        locinfo: loc_126 ;
        LocInfoE loc_128 (!{PtrOp} (LocInfoE loc_129 ("out"))) <-{ IntOp i32 }
          LocInfoE loc_130 (i2v 1 i32) ;
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
        locinfo: loc_134 ;
        expr: (LocInfoE loc_134 (Call (LocInfoE loc_141 (global_init_int)) [@{expr} LocInfoE loc_142 (&(LocInfoE loc_143 ("i"))) ])) ;
        locinfo: loc_135 ;
        expr: (LocInfoE loc_135 (Call (LocInfoE loc_137 (global_init_int)) [@{expr} LocInfoE loc_138 (&(LocInfoE loc_139 ("i"))) ])) ;
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
        locinfo: loc_146 ;
        LocInfoE loc_152 (!{PtrOp} (LocInfoE loc_153 ("out"))) <-{ StructOp struct_basic ([ IntOp i32 ; IntOp i32 ]) }
          StructInit struct_basic [
            ("a", LocInfoE loc_157 (i2v 1 i32) : expr) ;
            ("b", i2v 0 i32 : expr)
          ] ;
        locinfo: loc_147 ;
        LocInfoE loc_148 ((LocInfoE loc_149 (!{PtrOp} (LocInfoE loc_150 ("out")))) at{struct_basic} "a") <-{ IntOp i32 }
          LocInfoE loc_147 ((LocInfoE loc_147 (use{IntOp i32} (LocInfoE loc_148 ((LocInfoE loc_149 (!{PtrOp} (LocInfoE loc_150 ("out")))) at{struct_basic} "a")))) +{IntOp i32, IntOp i32} (LocInfoE loc_147 (i2v 1 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
