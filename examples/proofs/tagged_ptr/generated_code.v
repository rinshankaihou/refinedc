From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section code.
  Definition file_0 : string := "examples/tagged_ptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 20 2 20 30.
  Definition loc_3 : location_info := LocationInfo file_0 21 2 21 45.
  Definition loc_4 : location_info := LocationInfo file_0 22 2 22 11.
  Definition loc_5 : location_info := LocationInfo file_0 22 9 22 10.
  Definition loc_6 : location_info := LocationInfo file_0 22 9 22 10.
  Definition loc_7 : location_info := LocationInfo file_0 21 20 21 44.
  Definition loc_8 : location_info := LocationInfo file_0 21 20 21 21.
  Definition loc_9 : location_info := LocationInfo file_0 21 20 21 21.
  Definition loc_10 : location_info := LocationInfo file_0 21 24 21 44.
  Definition loc_11 : location_info := LocationInfo file_0 21 25 21 39.
  Definition loc_12 : location_info := LocationInfo file_0 21 26 21 30.
  Definition loc_13 : location_info := LocationInfo file_0 21 34 21 38.
  Definition loc_14 : location_info := LocationInfo file_0 21 42 21 43.
  Definition loc_17 : location_info := LocationInfo file_0 20 16 20 29.
  Definition loc_18 : location_info := LocationInfo file_0 20 28 20 29.
  Definition loc_19 : location_info := LocationInfo file_0 20 28 20 29.
  Definition loc_24 : location_info := LocationInfo file_0 31 2 31 30.
  Definition loc_25 : location_info := LocationInfo file_0 32 2 32 53.
  Definition loc_26 : location_info := LocationInfo file_0 33 2 33 50.
  Definition loc_27 : location_info := LocationInfo file_0 34 2 34 11.
  Definition loc_28 : location_info := LocationInfo file_0 34 9 34 10.
  Definition loc_29 : location_info := LocationInfo file_0 34 9 34 10.
  Definition loc_30 : location_info := LocationInfo file_0 33 12 33 49.
  Definition loc_31 : location_info := LocationInfo file_0 33 12 33 35.
  Definition loc_32 : location_info := LocationInfo file_0 33 36 33 43.
  Definition loc_33 : location_info := LocationInfo file_0 33 36 33 43.
  Definition loc_34 : location_info := LocationInfo file_0 33 45 33 48.
  Definition loc_35 : location_info := LocationInfo file_0 33 45 33 48.
  Definition loc_38 : location_info := LocationInfo file_0 32 20 32 52.
  Definition loc_39 : location_info := LocationInfo file_0 32 20 32 48.
  Definition loc_40 : location_info := LocationInfo file_0 32 21 32 22.
  Definition loc_41 : location_info := LocationInfo file_0 32 21 32 22.
  Definition loc_42 : location_info := LocationInfo file_0 32 25 32 47.
  Definition loc_43 : location_info := LocationInfo file_0 32 27 32 47.
  Definition loc_44 : location_info := LocationInfo file_0 32 28 32 42.
  Definition loc_45 : location_info := LocationInfo file_0 32 29 32 33.
  Definition loc_46 : location_info := LocationInfo file_0 32 37 32 41.
  Definition loc_47 : location_info := LocationInfo file_0 32 45 32 46.
  Definition loc_48 : location_info := LocationInfo file_0 32 51 32 52.
  Definition loc_49 : location_info := LocationInfo file_0 32 51 32 52.
  Definition loc_52 : location_info := LocationInfo file_0 31 16 31 29.
  Definition loc_53 : location_info := LocationInfo file_0 31 28 31 29.
  Definition loc_54 : location_info := LocationInfo file_0 31 28 31 29.
  Definition loc_59 : location_info := LocationInfo file_0 42 2 42 19.
  Definition loc_60 : location_info := LocationInfo file_0 42 9 42 18.
  Definition loc_61 : location_info := LocationInfo file_0 42 9 42 12.
  Definition loc_62 : location_info := LocationInfo file_0 42 9 42 12.
  Definition loc_63 : location_info := LocationInfo file_0 42 13 42 14.
  Definition loc_64 : location_info := LocationInfo file_0 42 13 42 14.
  Definition loc_65 : location_info := LocationInfo file_0 42 16 42 17.
  Definition loc_68 : location_info := LocationInfo file_0 50 2 50 30.
  Definition loc_69 : location_info := LocationInfo file_0 51 2 51 64.
  Definition loc_70 : location_info := LocationInfo file_0 51 9 51 63.
  Definition loc_71 : location_info := LocationInfo file_0 51 9 51 32.
  Definition loc_72 : location_info := LocationInfo file_0 51 33 51 57.
  Definition loc_73 : location_info := LocationInfo file_0 51 34 51 35.
  Definition loc_74 : location_info := LocationInfo file_0 51 34 51 35.
  Definition loc_75 : location_info := LocationInfo file_0 51 38 51 56.
  Definition loc_76 : location_info := LocationInfo file_0 51 38 51 39.
  Definition loc_77 : location_info := LocationInfo file_0 51 38 51 39.
  Definition loc_78 : location_info := LocationInfo file_0 51 42 51 56.
  Definition loc_79 : location_info := LocationInfo file_0 51 43 51 47.
  Definition loc_80 : location_info := LocationInfo file_0 51 51 51 55.
  Definition loc_81 : location_info := LocationInfo file_0 51 59 51 62.
  Definition loc_82 : location_info := LocationInfo file_0 51 59 51 62.
  Definition loc_83 : location_info := LocationInfo file_0 50 16 50 29.
  Definition loc_84 : location_info := LocationInfo file_0 50 28 50 29.
  Definition loc_85 : location_info := LocationInfo file_0 50 28 50 29.
  Definition loc_90 : location_info := LocationInfo file_0 56 2 56 15.
  Definition loc_91 : location_info := LocationInfo file_0 58 2 58 24.
  Definition loc_92 : location_info := LocationInfo file_0 59 2 59 26.
  Definition loc_93 : location_info := LocationInfo file_0 61 2 61 36.
  Definition loc_94 : location_info := LocationInfo file_0 62 2 62 13.
  Definition loc_95 : location_info := LocationInfo file_0 62 9 62 12.
  Definition loc_96 : location_info := LocationInfo file_0 62 9 62 12.
  Definition loc_97 : location_info := LocationInfo file_0 62 10 62 12.
  Definition loc_98 : location_info := LocationInfo file_0 62 10 62 12.
  Definition loc_99 : location_info := LocationInfo file_0 61 15 61 35.
  Definition loc_100 : location_info := LocationInfo file_0 61 26 61 35.
  Definition loc_101 : location_info := LocationInfo file_0 61 26 61 31.
  Definition loc_102 : location_info := LocationInfo file_0 61 26 61 31.
  Definition loc_103 : location_info := LocationInfo file_0 61 32 61 34.
  Definition loc_104 : location_info := LocationInfo file_0 61 32 61 34.
  Definition loc_107 : location_info := LocationInfo file_0 59 9 59 24.
  Definition loc_108 : location_info := LocationInfo file_0 59 9 59 19.
  Definition loc_109 : location_info := LocationInfo file_0 59 9 59 15.
  Definition loc_110 : location_info := LocationInfo file_0 59 9 59 15.
  Definition loc_111 : location_info := LocationInfo file_0 59 16 59 18.
  Definition loc_112 : location_info := LocationInfo file_0 59 16 59 18.
  Definition loc_113 : location_info := LocationInfo file_0 59 23 59 24.
  Definition loc_114 : location_info := LocationInfo file_0 58 13 58 23.
  Definition loc_115 : location_info := LocationInfo file_0 58 13 58 16.
  Definition loc_116 : location_info := LocationInfo file_0 58 13 58 16.
  Definition loc_117 : location_info := LocationInfo file_0 58 17 58 19.
  Definition loc_118 : location_info := LocationInfo file_0 58 18 58 19.
  Definition loc_119 : location_info := LocationInfo file_0 58 21 58 22.
  Definition loc_122 : location_info := LocationInfo file_0 56 13 56 14.
  Definition loc_127 : location_info := LocationInfo file_0 71 2 71 30.
  Definition loc_128 : location_info := LocationInfo file_0 72 2 72 33.
  Definition loc_129 : location_info := LocationInfo file_0 72 9 72 32.
  Definition loc_130 : location_info := LocationInfo file_0 72 9 72 27.
  Definition loc_131 : location_info := LocationInfo file_0 72 9 72 10.
  Definition loc_132 : location_info := LocationInfo file_0 72 9 72 10.
  Definition loc_133 : location_info := LocationInfo file_0 72 13 72 27.
  Definition loc_134 : location_info := LocationInfo file_0 72 14 72 18.
  Definition loc_135 : location_info := LocationInfo file_0 72 22 72 26.
  Definition loc_136 : location_info := LocationInfo file_0 72 31 72 32.
  Definition loc_137 : location_info := LocationInfo file_0 71 16 71 29.
  Definition loc_138 : location_info := LocationInfo file_0 71 28 71 29.
  Definition loc_139 : location_info := LocationInfo file_0 71 28 71 29.

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
          LocInfoE loc_17 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_18 (use{void*} (LocInfoE loc_19 ("p"))))) ;
        "t" <-{ it_layout u8 }
          LocInfoE loc_7 (UnOp (CastOp $ IntOp u8) (IntOp uintptr_t) (LocInfoE loc_7 ((LocInfoE loc_8 (use{it_layout uintptr_t} (LocInfoE loc_9 ("i")))) &{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_10 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_10 ((LocInfoE loc_11 ((LocInfoE loc_12 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_13 (i2v 3 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_14 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_14 (i2v 1 i32))))))))))) ;
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 (use{it_layout u8} (LocInfoE loc_6 ("t"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [tag]. *)
  Definition impl_tag : function := {|
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
          LocInfoE loc_52 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_53 (use{void*} (LocInfoE loc_54 ("p"))))) ;
        "new_i" <-{ it_layout uintptr_t }
          LocInfoE loc_38 ((LocInfoE loc_39 ((LocInfoE loc_40 (use{it_layout uintptr_t} (LocInfoE loc_41 ("i")))) &{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_42 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_42 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_43 ((LocInfoE loc_44 ((LocInfoE loc_45 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_46 (i2v 3 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_47 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_47 (i2v 1 i32)))))))))))) |{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_48 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_48 (use{it_layout u8} (LocInfoE loc_49 ("t"))))))) ;
        "q" <-{ void* }
          LocInfoE loc_30 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_32 (use{it_layout uintptr_t} (LocInfoE loc_33 ("new_i")))) (LocInfoE loc_34 (use{void*} (LocInfoE loc_35 ("p"))))) ;
        locinfo: loc_27 ;
        Return (LocInfoE loc_28 (use{void*} (LocInfoE loc_29 ("q"))))
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
        locinfo: loc_59 ;
        Return (LocInfoE loc_60 (Call (LocInfoE loc_62 (global_tag)) [@{expr} LocInfoE loc_63 (use{void*} (LocInfoE loc_64 ("p"))) ;
               LocInfoE loc_65 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_65 (i2v 0 i32))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [untag2]. *)
  Definition impl_untag2 : function := {|
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
          LocInfoE loc_83 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_84 (use{void*} (LocInfoE loc_85 ("p"))))) ;
        locinfo: loc_69 ;
        Return (LocInfoE loc_70 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_72 ((LocInfoE loc_73 (use{it_layout uintptr_t} (LocInfoE loc_74 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_75 ((LocInfoE loc_76 (use{it_layout uintptr_t} (LocInfoE loc_77 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_78 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_78 ((LocInfoE loc_79 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_80 (i2v 3 u64)))))))))) (LocInfoE loc_81 (use{void*} (LocInfoE loc_82 ("p"))))))
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
          LocInfoE loc_122 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_122 (i2v 0 i32))) ;
        "tp" <-{ void* }
          LocInfoE loc_114 (Call (LocInfoE loc_116 (global_tag)) [@{expr} LocInfoE loc_117 (&(LocInfoE loc_118 ("x"))) ;
          LocInfoE loc_119 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_119 (i2v 1 i32))) ]) ;
        locinfo: loc_92 ;
        assert: (LocInfoE loc_107 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_107 ((LocInfoE loc_108 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_108 (Call (LocInfoE loc_110 (global_tag_of)) [@{expr} LocInfoE loc_111 (use{void*} (LocInfoE loc_112 ("tp"))) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_113 (i2v 1 i32)))))) ;
        "px" <-{ void* }
          LocInfoE loc_99 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_100 (Call (LocInfoE loc_102 (global_untag)) [@{expr} LocInfoE loc_103 (use{void*} (LocInfoE loc_104 ("tp"))) ]))) ;
        locinfo: loc_94 ;
        Return (LocInfoE loc_95 (use{it_layout size_t} (LocInfoE loc_97 (!{void*} (LocInfoE loc_98 ("px"))))))
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
          LocInfoE loc_137 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_138 (use{void*} (LocInfoE loc_139 ("p"))))) ;
        locinfo: loc_128 ;
        Return (LocInfoE loc_129 ((LocInfoE loc_130 ((LocInfoE loc_131 (use{it_layout uintptr_t} (LocInfoE loc_132 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_133 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_133 ((LocInfoE loc_134 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_135 (i2v 3 u64)))))))) ={IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_136 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_136 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.
End code.
