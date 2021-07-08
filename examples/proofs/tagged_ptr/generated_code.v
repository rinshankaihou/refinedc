From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/tagged_ptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 20 2 20 30.
  Definition loc_12 : location_info := LocationInfo file_1 21 2 21 45.
  Definition loc_13 : location_info := LocationInfo file_1 22 2 22 11.
  Definition loc_14 : location_info := LocationInfo file_1 22 9 22 10.
  Definition loc_15 : location_info := LocationInfo file_1 22 9 22 10.
  Definition loc_16 : location_info := LocationInfo file_1 21 20 21 44.
  Definition loc_17 : location_info := LocationInfo file_1 21 20 21 21.
  Definition loc_18 : location_info := LocationInfo file_1 21 20 21 21.
  Definition loc_19 : location_info := LocationInfo file_1 21 24 21 44.
  Definition loc_20 : location_info := LocationInfo file_1 21 25 21 39.
  Definition loc_21 : location_info := LocationInfo file_1 21 26 21 30.
  Definition loc_22 : location_info := LocationInfo file_1 21 34 21 38.
  Definition loc_23 : location_info := LocationInfo file_1 21 42 21 43.
  Definition loc_26 : location_info := LocationInfo file_1 20 16 20 29.
  Definition loc_27 : location_info := LocationInfo file_1 20 28 20 29.
  Definition loc_28 : location_info := LocationInfo file_1 20 28 20 29.
  Definition loc_33 : location_info := LocationInfo file_1 31 2 31 30.
  Definition loc_34 : location_info := LocationInfo file_1 32 2 32 53.
  Definition loc_35 : location_info := LocationInfo file_1 33 2 33 36.
  Definition loc_36 : location_info := LocationInfo file_1 34 2 34 11.
  Definition loc_37 : location_info := LocationInfo file_1 34 9 34 10.
  Definition loc_38 : location_info := LocationInfo file_1 34 9 34 10.
  Definition loc_39 : location_info := LocationInfo file_1 33 12 33 35.
  Definition loc_40 : location_info := LocationInfo file_1 33 12 33 25.
  Definition loc_41 : location_info := LocationInfo file_1 33 12 33 25.
  Definition loc_42 : location_info := LocationInfo file_1 33 26 33 31.
  Definition loc_43 : location_info := LocationInfo file_1 33 26 33 31.
  Definition loc_44 : location_info := LocationInfo file_1 33 33 33 34.
  Definition loc_45 : location_info := LocationInfo file_1 33 33 33 34.
  Definition loc_48 : location_info := LocationInfo file_1 32 20 32 52.
  Definition loc_49 : location_info := LocationInfo file_1 32 20 32 48.
  Definition loc_50 : location_info := LocationInfo file_1 32 21 32 22.
  Definition loc_51 : location_info := LocationInfo file_1 32 21 32 22.
  Definition loc_52 : location_info := LocationInfo file_1 32 25 32 47.
  Definition loc_53 : location_info := LocationInfo file_1 32 27 32 47.
  Definition loc_54 : location_info := LocationInfo file_1 32 28 32 42.
  Definition loc_55 : location_info := LocationInfo file_1 32 29 32 33.
  Definition loc_56 : location_info := LocationInfo file_1 32 37 32 41.
  Definition loc_57 : location_info := LocationInfo file_1 32 45 32 46.
  Definition loc_58 : location_info := LocationInfo file_1 32 51 32 52.
  Definition loc_59 : location_info := LocationInfo file_1 32 51 32 52.
  Definition loc_62 : location_info := LocationInfo file_1 31 16 31 29.
  Definition loc_63 : location_info := LocationInfo file_1 31 28 31 29.
  Definition loc_64 : location_info := LocationInfo file_1 31 28 31 29.
  Definition loc_69 : location_info := LocationInfo file_1 42 2 42 19.
  Definition loc_70 : location_info := LocationInfo file_1 42 9 42 18.
  Definition loc_71 : location_info := LocationInfo file_1 42 9 42 12.
  Definition loc_72 : location_info := LocationInfo file_1 42 9 42 12.
  Definition loc_73 : location_info := LocationInfo file_1 42 13 42 14.
  Definition loc_74 : location_info := LocationInfo file_1 42 13 42 14.
  Definition loc_75 : location_info := LocationInfo file_1 42 16 42 17.
  Definition loc_78 : location_info := LocationInfo file_1 50 2 50 30.
  Definition loc_79 : location_info := LocationInfo file_1 51 2 51 50.
  Definition loc_80 : location_info := LocationInfo file_1 51 9 51 49.
  Definition loc_81 : location_info := LocationInfo file_1 51 9 51 22.
  Definition loc_82 : location_info := LocationInfo file_1 51 9 51 22.
  Definition loc_83 : location_info := LocationInfo file_1 51 23 51 45.
  Definition loc_84 : location_info := LocationInfo file_1 51 23 51 24.
  Definition loc_85 : location_info := LocationInfo file_1 51 23 51 24.
  Definition loc_86 : location_info := LocationInfo file_1 51 27 51 45.
  Definition loc_87 : location_info := LocationInfo file_1 51 27 51 28.
  Definition loc_88 : location_info := LocationInfo file_1 51 27 51 28.
  Definition loc_89 : location_info := LocationInfo file_1 51 31 51 45.
  Definition loc_90 : location_info := LocationInfo file_1 51 32 51 36.
  Definition loc_91 : location_info := LocationInfo file_1 51 40 51 44.
  Definition loc_92 : location_info := LocationInfo file_1 51 47 51 48.
  Definition loc_93 : location_info := LocationInfo file_1 51 47 51 48.
  Definition loc_94 : location_info := LocationInfo file_1 50 16 50 29.
  Definition loc_95 : location_info := LocationInfo file_1 50 28 50 29.
  Definition loc_96 : location_info := LocationInfo file_1 50 28 50 29.
  Definition loc_101 : location_info := LocationInfo file_1 56 2 56 15.
  Definition loc_102 : location_info := LocationInfo file_1 58 2 58 24.
  Definition loc_103 : location_info := LocationInfo file_1 59 2 59 26.
  Definition loc_104 : location_info := LocationInfo file_1 61 2 61 36.
  Definition loc_105 : location_info := LocationInfo file_1 62 2 62 13.
  Definition loc_106 : location_info := LocationInfo file_1 62 9 62 12.
  Definition loc_107 : location_info := LocationInfo file_1 62 9 62 12.
  Definition loc_108 : location_info := LocationInfo file_1 62 10 62 12.
  Definition loc_109 : location_info := LocationInfo file_1 62 10 62 12.
  Definition loc_110 : location_info := LocationInfo file_1 61 15 61 35.
  Definition loc_111 : location_info := LocationInfo file_1 61 26 61 35.
  Definition loc_112 : location_info := LocationInfo file_1 61 26 61 31.
  Definition loc_113 : location_info := LocationInfo file_1 61 26 61 31.
  Definition loc_114 : location_info := LocationInfo file_1 61 32 61 34.
  Definition loc_115 : location_info := LocationInfo file_1 61 32 61 34.
  Definition loc_118 : location_info := LocationInfo file_1 59 9 59 24.
  Definition loc_119 : location_info := LocationInfo file_1 59 9 59 19.
  Definition loc_120 : location_info := LocationInfo file_1 59 9 59 15.
  Definition loc_121 : location_info := LocationInfo file_1 59 9 59 15.
  Definition loc_122 : location_info := LocationInfo file_1 59 16 59 18.
  Definition loc_123 : location_info := LocationInfo file_1 59 16 59 18.
  Definition loc_124 : location_info := LocationInfo file_1 59 23 59 24.
  Definition loc_125 : location_info := LocationInfo file_1 58 13 58 23.
  Definition loc_126 : location_info := LocationInfo file_1 58 13 58 16.
  Definition loc_127 : location_info := LocationInfo file_1 58 13 58 16.
  Definition loc_128 : location_info := LocationInfo file_1 58 17 58 19.
  Definition loc_129 : location_info := LocationInfo file_1 58 18 58 19.
  Definition loc_130 : location_info := LocationInfo file_1 58 21 58 22.
  Definition loc_133 : location_info := LocationInfo file_1 56 13 56 14.
  Definition loc_138 : location_info := LocationInfo file_1 71 2 71 30.
  Definition loc_139 : location_info := LocationInfo file_1 72 2 72 33.
  Definition loc_140 : location_info := LocationInfo file_1 72 9 72 32.
  Definition loc_141 : location_info := LocationInfo file_1 72 9 72 27.
  Definition loc_142 : location_info := LocationInfo file_1 72 9 72 10.
  Definition loc_143 : location_info := LocationInfo file_1 72 9 72 10.
  Definition loc_144 : location_info := LocationInfo file_1 72 13 72 27.
  Definition loc_145 : location_info := LocationInfo file_1 72 14 72 18.
  Definition loc_146 : location_info := LocationInfo file_1 72 22 72 26.
  Definition loc_147 : location_info := LocationInfo file_1 72 31 72 32.
  Definition loc_148 : location_info := LocationInfo file_1 71 16 71 29.
  Definition loc_149 : location_info := LocationInfo file_1 71 28 71 29.
  Definition loc_150 : location_info := LocationInfo file_1 71 28 71 29.

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

  (* Definition of function [tag_of]. *)
  Definition impl_tag_of : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("t", it_layout u8)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_26 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_27 (use{void*} (LocInfoE loc_28 ("p"))))) ;
        "t" <-{ it_layout u8 }
          LocInfoE loc_16 (UnOp (CastOp $ IntOp u8) (IntOp uintptr_t) (LocInfoE loc_16 ((LocInfoE loc_17 (use{it_layout uintptr_t} (LocInfoE loc_18 ("i")))) &{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_19 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_19 ((LocInfoE loc_20 ((LocInfoE loc_21 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_22 (i2v 3 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_23 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_23 (i2v 1 i32))))))))))) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (use{it_layout u8} (LocInfoE loc_15 ("t"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [tag]. *)
  Definition impl_tag (global_copy_alloc_id : loc): function := {|
    f_args := [
      ("p", void*);
      ("t", it_layout u8)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("new_i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_62 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_63 (use{void*} (LocInfoE loc_64 ("p"))))) ;
        "new_i" <-{ it_layout uintptr_t }
          LocInfoE loc_48 ((LocInfoE loc_49 ((LocInfoE loc_50 (use{it_layout uintptr_t} (LocInfoE loc_51 ("i")))) &{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_52 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_52 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_53 ((LocInfoE loc_54 ((LocInfoE loc_55 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_56 (i2v 3 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_57 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_57 (i2v 1 i32)))))))))))) |{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_58 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_58 (use{it_layout u8} (LocInfoE loc_59 ("t"))))))) ;
        "q" <-{ void* }
          LocInfoE loc_39 (Call (LocInfoE loc_41 (global_copy_alloc_id)) [@{expr} LocInfoE loc_42 (use{it_layout uintptr_t} (LocInfoE loc_43 ("new_i"))) ;
          LocInfoE loc_44 (use{void*} (LocInfoE loc_45 ("p"))) ]) ;
        locinfo: loc_36 ;
        Return (LocInfoE loc_37 (use{void*} (LocInfoE loc_38 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [untag]. *)
  Definition impl_untag (global_tag : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_69 ;
        Return (LocInfoE loc_70 (Call (LocInfoE loc_72 (global_tag)) [@{expr} LocInfoE loc_73 (use{void*} (LocInfoE loc_74 ("p"))) ;
               LocInfoE loc_75 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_75 (i2v 0 i32))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [untag2]. *)
  Definition impl_untag2 (global_copy_alloc_id : loc): function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_94 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_95 (use{void*} (LocInfoE loc_96 ("p"))))) ;
        locinfo: loc_79 ;
        Return (LocInfoE loc_80 (Call (LocInfoE loc_82 (global_copy_alloc_id)) [@{expr} LocInfoE loc_83 ((LocInfoE loc_84 (use{it_layout uintptr_t} (LocInfoE loc_85 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_86 ((LocInfoE loc_87 (use{it_layout uintptr_t} (LocInfoE loc_88 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_89 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_89 ((LocInfoE loc_90 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_91 (i2v 3 u64))))))))) ;
               LocInfoE loc_92 (use{void*} (LocInfoE loc_93 ("p"))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test (global_tag global_tag_of global_untag : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("tp", void*);
      ("x", it_layout size_t);
      ("px", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "x" <-{ it_layout size_t }
          LocInfoE loc_133 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_133 (i2v 0 i32))) ;
        "tp" <-{ void* }
          LocInfoE loc_125 (Call (LocInfoE loc_127 (global_tag)) [@{expr} LocInfoE loc_128 (&(LocInfoE loc_129 ("x"))) ;
          LocInfoE loc_130 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_130 (i2v 1 i32))) ]) ;
        locinfo: loc_103 ;
        assert: (LocInfoE loc_118 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_118 ((LocInfoE loc_119 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_119 (Call (LocInfoE loc_121 (global_tag_of)) [@{expr} LocInfoE loc_122 (use{void*} (LocInfoE loc_123 ("tp"))) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_124 (i2v 1 i32)))))) ;
        "px" <-{ void* }
          LocInfoE loc_110 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_111 (Call (LocInfoE loc_113 (global_untag)) [@{expr} LocInfoE loc_114 (use{void*} (LocInfoE loc_115 ("tp"))) ]))) ;
        locinfo: loc_105 ;
        Return (LocInfoE loc_106 (use{it_layout size_t} (LocInfoE loc_108 (!{void*} (LocInfoE loc_109 ("px"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [is_aligned]. *)
  Definition impl_is_aligned : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_148 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_149 (use{void*} (LocInfoE loc_150 ("p"))))) ;
        locinfo: loc_139 ;
        Return (LocInfoE loc_140 ((LocInfoE loc_141 ((LocInfoE loc_142 (use{it_layout uintptr_t} (LocInfoE loc_143 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_144 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_144 ((LocInfoE loc_145 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_146 (i2v 3 u64)))))))) ={IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_147 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_147 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.
End code.
