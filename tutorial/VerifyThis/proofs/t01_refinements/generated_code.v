From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t01_refinements.c]. *)
Section code.
  Definition file_0 : string := "tutorial/VerifyThis/t01_refinements.c".
  Definition file_1 : string := "include/refinedc.h".
  Definition loc_2 : location_info := LocationInfo file_1 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_1 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_1 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_1 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_1 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 9 2 9 21.
  Definition loc_12 : location_info := LocationInfo file_0 9 9 9 20.
  Definition loc_13 : location_info := LocationInfo file_0 9 9 9 16.
  Definition loc_14 : location_info := LocationInfo file_0 9 10 9 11.
  Definition loc_15 : location_info := LocationInfo file_0 9 10 9 11.
  Definition loc_16 : location_info := LocationInfo file_0 9 14 9 15.
  Definition loc_17 : location_info := LocationInfo file_0 9 14 9 15.
  Definition loc_18 : location_info := LocationInfo file_0 9 19 9 20.
  Definition loc_21 : location_info := LocationInfo file_0 22 2 22 21.
  Definition loc_22 : location_info := LocationInfo file_0 22 9 22 20.
  Definition loc_23 : location_info := LocationInfo file_0 22 9 22 16.
  Definition loc_24 : location_info := LocationInfo file_0 22 10 22 11.
  Definition loc_25 : location_info := LocationInfo file_0 22 10 22 11.
  Definition loc_26 : location_info := LocationInfo file_0 22 14 22 15.
  Definition loc_27 : location_info := LocationInfo file_0 22 14 22 15.
  Definition loc_28 : location_info := LocationInfo file_0 22 19 22 20.
  Definition loc_31 : location_info := LocationInfo file_0 53 2 53 37.
  Definition loc_32 : location_info := LocationInfo file_0 54 2 54 38.
  Definition loc_33 : location_info := LocationInfo file_0 55 2 55 32.
  Definition loc_34 : location_info := LocationInfo file_0 55 9 55 31.
  Definition loc_35 : location_info := LocationInfo file_0 55 9 55 12.
  Definition loc_36 : location_info := LocationInfo file_0 55 9 55 12.
  Definition loc_37 : location_info := LocationInfo file_0 55 15 55 31.
  Definition loc_38 : location_info := LocationInfo file_0 55 15 55 27.
  Definition loc_39 : location_info := LocationInfo file_0 55 16 55 20.
  Definition loc_40 : location_info := LocationInfo file_0 55 16 55 20.
  Definition loc_41 : location_info := LocationInfo file_0 55 23 55 26.
  Definition loc_42 : location_info := LocationInfo file_0 55 23 55 26.
  Definition loc_43 : location_info := LocationInfo file_0 55 30 55 31.
  Definition loc_44 : location_info := LocationInfo file_0 54 22 54 37.
  Definition loc_45 : location_info := LocationInfo file_0 54 22 54 29.
  Definition loc_46 : location_info := LocationInfo file_0 54 23 54 24.
  Definition loc_47 : location_info := LocationInfo file_0 54 23 54 24.
  Definition loc_48 : location_info := LocationInfo file_0 54 27 54 28.
  Definition loc_49 : location_info := LocationInfo file_0 54 27 54 28.
  Definition loc_50 : location_info := LocationInfo file_0 54 32 54 33.
  Definition loc_51 : location_info := LocationInfo file_0 54 32 54 33.
  Definition loc_52 : location_info := LocationInfo file_0 54 36 54 37.
  Definition loc_53 : location_info := LocationInfo file_0 54 36 54 37.
  Definition loc_56 : location_info := LocationInfo file_0 53 21 53 36.
  Definition loc_57 : location_info := LocationInfo file_0 53 21 53 28.
  Definition loc_58 : location_info := LocationInfo file_0 53 22 53 23.
  Definition loc_59 : location_info := LocationInfo file_0 53 22 53 23.
  Definition loc_60 : location_info := LocationInfo file_0 53 26 53 27.
  Definition loc_61 : location_info := LocationInfo file_0 53 26 53 27.
  Definition loc_62 : location_info := LocationInfo file_0 53 31 53 32.
  Definition loc_63 : location_info := LocationInfo file_0 53 31 53 32.
  Definition loc_64 : location_info := LocationInfo file_0 53 35 53 36.
  Definition loc_65 : location_info := LocationInfo file_0 53 35 53 36.
  Definition loc_70 : location_info := LocationInfo file_0 87 2 87 37.
  Definition loc_71 : location_info := LocationInfo file_0 88 2 88 38.
  Definition loc_72 : location_info := LocationInfo file_0 89 2 89 32.
  Definition loc_73 : location_info := LocationInfo file_0 89 9 89 31.
  Definition loc_74 : location_info := LocationInfo file_0 89 9 89 12.
  Definition loc_75 : location_info := LocationInfo file_0 89 9 89 12.
  Definition loc_76 : location_info := LocationInfo file_0 89 15 89 31.
  Definition loc_77 : location_info := LocationInfo file_0 89 15 89 27.
  Definition loc_78 : location_info := LocationInfo file_0 89 16 89 20.
  Definition loc_79 : location_info := LocationInfo file_0 89 16 89 20.
  Definition loc_80 : location_info := LocationInfo file_0 89 23 89 26.
  Definition loc_81 : location_info := LocationInfo file_0 89 23 89 26.
  Definition loc_82 : location_info := LocationInfo file_0 89 30 89 31.
  Definition loc_83 : location_info := LocationInfo file_0 88 22 88 37.
  Definition loc_84 : location_info := LocationInfo file_0 88 22 88 29.
  Definition loc_85 : location_info := LocationInfo file_0 88 23 88 24.
  Definition loc_86 : location_info := LocationInfo file_0 88 23 88 24.
  Definition loc_87 : location_info := LocationInfo file_0 88 27 88 28.
  Definition loc_88 : location_info := LocationInfo file_0 88 27 88 28.
  Definition loc_89 : location_info := LocationInfo file_0 88 32 88 33.
  Definition loc_90 : location_info := LocationInfo file_0 88 32 88 33.
  Definition loc_91 : location_info := LocationInfo file_0 88 36 88 37.
  Definition loc_92 : location_info := LocationInfo file_0 88 36 88 37.
  Definition loc_95 : location_info := LocationInfo file_0 87 21 87 36.
  Definition loc_96 : location_info := LocationInfo file_0 87 21 87 28.
  Definition loc_97 : location_info := LocationInfo file_0 87 22 87 23.
  Definition loc_98 : location_info := LocationInfo file_0 87 22 87 23.
  Definition loc_99 : location_info := LocationInfo file_0 87 26 87 27.
  Definition loc_100 : location_info := LocationInfo file_0 87 26 87 27.
  Definition loc_101 : location_info := LocationInfo file_0 87 31 87 32.
  Definition loc_102 : location_info := LocationInfo file_0 87 31 87 32.
  Definition loc_103 : location_info := LocationInfo file_0 87 35 87 36.
  Definition loc_104 : location_info := LocationInfo file_0 87 35 87 36.
  Definition loc_109 : location_info := LocationInfo file_0 98 2 98 37.
  Definition loc_110 : location_info := LocationInfo file_0 99 2 99 38.
  Definition loc_111 : location_info := LocationInfo file_0 100 2 100 32.
  Definition loc_112 : location_info := LocationInfo file_0 100 9 100 31.
  Definition loc_113 : location_info := LocationInfo file_0 100 9 100 12.
  Definition loc_114 : location_info := LocationInfo file_0 100 9 100 12.
  Definition loc_115 : location_info := LocationInfo file_0 100 15 100 31.
  Definition loc_116 : location_info := LocationInfo file_0 100 15 100 27.
  Definition loc_117 : location_info := LocationInfo file_0 100 16 100 20.
  Definition loc_118 : location_info := LocationInfo file_0 100 16 100 20.
  Definition loc_119 : location_info := LocationInfo file_0 100 23 100 26.
  Definition loc_120 : location_info := LocationInfo file_0 100 23 100 26.
  Definition loc_121 : location_info := LocationInfo file_0 100 30 100 31.
  Definition loc_122 : location_info := LocationInfo file_0 99 22 99 37.
  Definition loc_123 : location_info := LocationInfo file_0 99 22 99 29.
  Definition loc_124 : location_info := LocationInfo file_0 99 23 99 24.
  Definition loc_125 : location_info := LocationInfo file_0 99 23 99 24.
  Definition loc_126 : location_info := LocationInfo file_0 99 27 99 28.
  Definition loc_127 : location_info := LocationInfo file_0 99 27 99 28.
  Definition loc_128 : location_info := LocationInfo file_0 99 32 99 33.
  Definition loc_129 : location_info := LocationInfo file_0 99 32 99 33.
  Definition loc_130 : location_info := LocationInfo file_0 99 36 99 37.
  Definition loc_131 : location_info := LocationInfo file_0 99 36 99 37.
  Definition loc_134 : location_info := LocationInfo file_0 98 21 98 36.
  Definition loc_135 : location_info := LocationInfo file_0 98 21 98 28.
  Definition loc_136 : location_info := LocationInfo file_0 98 22 98 23.
  Definition loc_137 : location_info := LocationInfo file_0 98 22 98 23.
  Definition loc_138 : location_info := LocationInfo file_0 98 26 98 27.
  Definition loc_139 : location_info := LocationInfo file_0 98 26 98 27.
  Definition loc_140 : location_info := LocationInfo file_0 98 31 98 32.
  Definition loc_141 : location_info := LocationInfo file_0 98 31 98 32.
  Definition loc_142 : location_info := LocationInfo file_0 98 35 98 36.
  Definition loc_143 : location_info := LocationInfo file_0 98 35 98 36.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
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

  (* Definition of function [avg_1]. *)
  Definition impl_avg_1 : function := {|
    f_args := [
      ("a", it_layout u32);
      ("b", it_layout u32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 ((LocInfoE loc_13 ((LocInfoE loc_14 (use{IntOp u32} (LocInfoE loc_15 ("a")))) +{IntOp u32, IntOp u32} (LocInfoE loc_16 (use{IntOp u32} (LocInfoE loc_17 ("b")))))) /{IntOp u32, IntOp u32} (LocInfoE loc_18 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_18 (i2v 2 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [avg_2]. *)
  Definition impl_avg_2 : function := {|
    f_args := [
      ("a", it_layout u32);
      ("b", it_layout u32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_21 ;
        Return (LocInfoE loc_22 ((LocInfoE loc_23 ((LocInfoE loc_24 (use{IntOp u32} (LocInfoE loc_25 ("a")))) +{IntOp u32, IntOp u32} (LocInfoE loc_26 (use{IntOp u32} (LocInfoE loc_27 ("b")))))) /{IntOp u32, IntOp u32} (LocInfoE loc_28 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_28 (i2v 2 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [avg_3]. *)
  Definition impl_avg_3 : function := {|
    f_args := [
      ("a", it_layout u32);
      ("b", it_layout u32)
    ];
    f_local_vars := [
      ("low", it_layout u32);
      ("high", it_layout u32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "low" <-{ IntOp u32 } LocInfoE loc_56 (IfE (IntOp i32)
          (LocInfoE loc_57 ((LocInfoE loc_58 (use{IntOp u32} (LocInfoE loc_59 ("a")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_60 (use{IntOp u32} (LocInfoE loc_61 ("b"))))))
          (LocInfoE loc_62 (use{IntOp u32} (LocInfoE loc_63 ("a"))))
          (LocInfoE loc_64 (use{IntOp u32} (LocInfoE loc_65 ("b"))))) ;
        "high" <-{ IntOp u32 } LocInfoE loc_44 (IfE (IntOp i32)
          (LocInfoE loc_45 ((LocInfoE loc_46 (use{IntOp u32} (LocInfoE loc_47 ("a")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_48 (use{IntOp u32} (LocInfoE loc_49 ("b"))))))
          (LocInfoE loc_50 (use{IntOp u32} (LocInfoE loc_51 ("b"))))
          (LocInfoE loc_52 (use{IntOp u32} (LocInfoE loc_53 ("a"))))) ;
        locinfo: loc_33 ;
        Return (LocInfoE loc_34 ((LocInfoE loc_35 (use{IntOp u32} (LocInfoE loc_36 ("low")))) +{IntOp u32, IntOp u32} (LocInfoE loc_37 ((LocInfoE loc_38 ((LocInfoE loc_39 (use{IntOp u32} (LocInfoE loc_40 ("high")))) -{IntOp u32, IntOp u32} (LocInfoE loc_41 (use{IntOp u32} (LocInfoE loc_42 ("low")))))) /{IntOp u32, IntOp u32} (LocInfoE loc_43 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_43 (i2v 2 i32))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [avg_4]. *)
  Definition impl_avg_4 : function := {|
    f_args := [
      ("a", it_layout u32);
      ("b", it_layout u32)
    ];
    f_local_vars := [
      ("low", it_layout u32);
      ("high", it_layout u32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "low" <-{ IntOp u32 } LocInfoE loc_95 (IfE (IntOp i32)
          (LocInfoE loc_96 ((LocInfoE loc_97 (use{IntOp u32} (LocInfoE loc_98 ("a")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_99 (use{IntOp u32} (LocInfoE loc_100 ("b"))))))
          (LocInfoE loc_101 (use{IntOp u32} (LocInfoE loc_102 ("a"))))
          (LocInfoE loc_103 (use{IntOp u32} (LocInfoE loc_104 ("b"))))) ;
        "high" <-{ IntOp u32 } LocInfoE loc_83 (IfE (IntOp i32)
          (LocInfoE loc_84 ((LocInfoE loc_85 (use{IntOp u32} (LocInfoE loc_86 ("a")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_87 (use{IntOp u32} (LocInfoE loc_88 ("b"))))))
          (LocInfoE loc_89 (use{IntOp u32} (LocInfoE loc_90 ("b"))))
          (LocInfoE loc_91 (use{IntOp u32} (LocInfoE loc_92 ("a"))))) ;
        locinfo: loc_72 ;
        Return (LocInfoE loc_73 ((LocInfoE loc_74 (use{IntOp u32} (LocInfoE loc_75 ("low")))) +{IntOp u32, IntOp u32} (LocInfoE loc_76 ((LocInfoE loc_77 ((LocInfoE loc_78 (use{IntOp u32} (LocInfoE loc_79 ("high")))) -{IntOp u32, IntOp u32} (LocInfoE loc_80 (use{IntOp u32} (LocInfoE loc_81 ("low")))))) /{IntOp u32, IntOp u32} (LocInfoE loc_82 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_82 (i2v 2 i32))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [avg_5]. *)
  Definition impl_avg_5 : function := {|
    f_args := [
      ("a", it_layout u32);
      ("b", it_layout u32)
    ];
    f_local_vars := [
      ("low", it_layout u32);
      ("high", it_layout u32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "low" <-{ IntOp u32 } LocInfoE loc_134 (IfE (IntOp i32)
          (LocInfoE loc_135 ((LocInfoE loc_136 (use{IntOp u32} (LocInfoE loc_137 ("a")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_138 (use{IntOp u32} (LocInfoE loc_139 ("b"))))))
          (LocInfoE loc_140 (use{IntOp u32} (LocInfoE loc_141 ("a"))))
          (LocInfoE loc_142 (use{IntOp u32} (LocInfoE loc_143 ("b"))))) ;
        "high" <-{ IntOp u32 } LocInfoE loc_122 (IfE (IntOp i32)
          (LocInfoE loc_123 ((LocInfoE loc_124 (use{IntOp u32} (LocInfoE loc_125 ("a")))) <{IntOp u32, IntOp u32, i32} (LocInfoE loc_126 (use{IntOp u32} (LocInfoE loc_127 ("b"))))))
          (LocInfoE loc_128 (use{IntOp u32} (LocInfoE loc_129 ("b"))))
          (LocInfoE loc_130 (use{IntOp u32} (LocInfoE loc_131 ("a"))))) ;
        locinfo: loc_111 ;
        Return (LocInfoE loc_112 ((LocInfoE loc_113 (use{IntOp u32} (LocInfoE loc_114 ("low")))) +{IntOp u32, IntOp u32} (LocInfoE loc_115 ((LocInfoE loc_116 ((LocInfoE loc_117 (use{IntOp u32} (LocInfoE loc_118 ("high")))) -{IntOp u32, IntOp u32} (LocInfoE loc_119 (use{IntOp u32} (LocInfoE loc_120 ("low")))))) /{IntOp u32, IntOp u32} (LocInfoE loc_121 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_121 (i2v 2 i32))))))))
      ]> $∅
    )%E
  |}.
End code.
