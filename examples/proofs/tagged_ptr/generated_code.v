From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section code.
  Definition file_0 : string := "examples/tagged_ptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 17 2 17 30.
  Definition loc_3 : location_info := LocationInfo file_0 18 2 18 33.
  Definition loc_4 : location_info := LocationInfo file_0 19 2 19 11.
  Definition loc_5 : location_info := LocationInfo file_0 19 9 19 10.
  Definition loc_6 : location_info := LocationInfo file_0 19 9 19 10.
  Definition loc_7 : location_info := LocationInfo file_0 18 20 18 32.
  Definition loc_8 : location_info := LocationInfo file_0 18 20 18 21.
  Definition loc_9 : location_info := LocationInfo file_0 18 20 18 21.
  Definition loc_10 : location_info := LocationInfo file_0 18 24 18 32.
  Definition loc_11 : location_info := LocationInfo file_0 18 25 18 26.
  Definition loc_12 : location_info := LocationInfo file_0 18 30 18 31.
  Definition loc_15 : location_info := LocationInfo file_0 17 16 17 29.
  Definition loc_16 : location_info := LocationInfo file_0 17 28 17 29.
  Definition loc_17 : location_info := LocationInfo file_0 17 28 17 29.
  Definition loc_22 : location_info := LocationInfo file_0 27 2 27 30.
  Definition loc_23 : location_info := LocationInfo file_0 28 2 28 41.
  Definition loc_24 : location_info := LocationInfo file_0 29 2 29 107.
  Definition loc_25 : location_info := LocationInfo file_0 30 2 30 11.
  Definition loc_26 : location_info := LocationInfo file_0 30 9 30 10.
  Definition loc_27 : location_info := LocationInfo file_0 30 9 30 10.
  Definition loc_28 : location_info := LocationInfo file_0 29 12 29 106.
  Definition loc_29 : location_info := LocationInfo file_0 29 38 29 41.
  Definition loc_30 : location_info := LocationInfo file_0 29 38 29 41.
  Definition loc_31 : location_info := LocationInfo file_0 29 43 29 50.
  Definition loc_32 : location_info := LocationInfo file_0 29 43 29 50.
  Definition loc_35 : location_info := LocationInfo file_0 28 20 28 40.
  Definition loc_36 : location_info := LocationInfo file_0 28 20 28 36.
  Definition loc_37 : location_info := LocationInfo file_0 28 20 28 21.
  Definition loc_38 : location_info := LocationInfo file_0 28 20 28 21.
  Definition loc_39 : location_info := LocationInfo file_0 28 24 28 36.
  Definition loc_40 : location_info := LocationInfo file_0 28 24 28 25.
  Definition loc_41 : location_info := LocationInfo file_0 28 24 28 25.
  Definition loc_42 : location_info := LocationInfo file_0 28 28 28 36.
  Definition loc_43 : location_info := LocationInfo file_0 28 29 28 30.
  Definition loc_44 : location_info := LocationInfo file_0 28 34 28 35.
  Definition loc_45 : location_info := LocationInfo file_0 28 39 28 40.
  Definition loc_46 : location_info := LocationInfo file_0 28 39 28 40.
  Definition loc_49 : location_info := LocationInfo file_0 27 16 27 29.
  Definition loc_50 : location_info := LocationInfo file_0 27 28 27 29.
  Definition loc_51 : location_info := LocationInfo file_0 27 28 27 29.
  Definition loc_56 : location_info := LocationInfo file_0 38 2 38 19.
  Definition loc_57 : location_info := LocationInfo file_0 38 9 38 18.
  Definition loc_58 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_59 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_60 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_61 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_62 : location_info := LocationInfo file_0 38 16 38 17.
  Definition loc_65 : location_info := LocationInfo file_0 46 2 46 30.
  Definition loc_66 : location_info := LocationInfo file_0 47 2 47 137.
  Definition loc_67 : location_info := LocationInfo file_0 47 9 47 136.
  Definition loc_68 : location_info := LocationInfo file_0 47 35 47 38.
  Definition loc_69 : location_info := LocationInfo file_0 47 35 47 38.
  Definition loc_70 : location_info := LocationInfo file_0 47 40 47 58.
  Definition loc_71 : location_info := LocationInfo file_0 47 41 47 42.
  Definition loc_72 : location_info := LocationInfo file_0 47 41 47 42.
  Definition loc_73 : location_info := LocationInfo file_0 47 45 47 57.
  Definition loc_74 : location_info := LocationInfo file_0 47 45 47 46.
  Definition loc_75 : location_info := LocationInfo file_0 47 45 47 46.
  Definition loc_76 : location_info := LocationInfo file_0 47 49 47 57.
  Definition loc_77 : location_info := LocationInfo file_0 47 50 47 51.
  Definition loc_78 : location_info := LocationInfo file_0 47 55 47 56.
  Definition loc_79 : location_info := LocationInfo file_0 46 16 46 29.
  Definition loc_80 : location_info := LocationInfo file_0 46 28 46 29.
  Definition loc_81 : location_info := LocationInfo file_0 46 28 46 29.
  Definition loc_86 : location_info := LocationInfo file_0 52 2 52 15.
  Definition loc_87 : location_info := LocationInfo file_0 54 2 54 24.
  Definition loc_88 : location_info := LocationInfo file_0 55 2 55 26.
  Definition loc_89 : location_info := LocationInfo file_0 57 2 57 36.
  Definition loc_90 : location_info := LocationInfo file_0 58 2 58 13.
  Definition loc_91 : location_info := LocationInfo file_0 58 9 58 12.
  Definition loc_92 : location_info := LocationInfo file_0 58 9 58 12.
  Definition loc_93 : location_info := LocationInfo file_0 58 10 58 12.
  Definition loc_94 : location_info := LocationInfo file_0 58 10 58 12.
  Definition loc_95 : location_info := LocationInfo file_0 57 15 57 35.
  Definition loc_96 : location_info := LocationInfo file_0 57 26 57 35.
  Definition loc_97 : location_info := LocationInfo file_0 57 26 57 31.
  Definition loc_98 : location_info := LocationInfo file_0 57 26 57 31.
  Definition loc_99 : location_info := LocationInfo file_0 57 32 57 34.
  Definition loc_100 : location_info := LocationInfo file_0 57 32 57 34.
  Definition loc_103 : location_info := LocationInfo file_0 55 9 55 24.
  Definition loc_104 : location_info := LocationInfo file_0 55 9 55 19.
  Definition loc_105 : location_info := LocationInfo file_0 55 9 55 15.
  Definition loc_106 : location_info := LocationInfo file_0 55 9 55 15.
  Definition loc_107 : location_info := LocationInfo file_0 55 16 55 18.
  Definition loc_108 : location_info := LocationInfo file_0 55 16 55 18.
  Definition loc_109 : location_info := LocationInfo file_0 55 23 55 24.
  Definition loc_110 : location_info := LocationInfo file_0 54 13 54 23.
  Definition loc_111 : location_info := LocationInfo file_0 54 13 54 16.
  Definition loc_112 : location_info := LocationInfo file_0 54 13 54 16.
  Definition loc_113 : location_info := LocationInfo file_0 54 17 54 19.
  Definition loc_114 : location_info := LocationInfo file_0 54 18 54 19.
  Definition loc_115 : location_info := LocationInfo file_0 54 21 54 22.
  Definition loc_118 : location_info := LocationInfo file_0 52 13 52 14.
  Definition loc_123 : location_info := LocationInfo file_0 67 2 67 30.
  Definition loc_124 : location_info := LocationInfo file_0 68 2 68 27.
  Definition loc_125 : location_info := LocationInfo file_0 68 9 68 26.
  Definition loc_126 : location_info := LocationInfo file_0 68 9 68 21.
  Definition loc_127 : location_info := LocationInfo file_0 68 9 68 10.
  Definition loc_128 : location_info := LocationInfo file_0 68 9 68 10.
  Definition loc_129 : location_info := LocationInfo file_0 68 13 68 21.
  Definition loc_130 : location_info := LocationInfo file_0 68 14 68 15.
  Definition loc_131 : location_info := LocationInfo file_0 68 19 68 20.
  Definition loc_132 : location_info := LocationInfo file_0 68 25 68 26.
  Definition loc_133 : location_info := LocationInfo file_0 67 16 67 29.
  Definition loc_134 : location_info := LocationInfo file_0 67 28 67 29.
  Definition loc_135 : location_info := LocationInfo file_0 67 28 67 29.

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
          LocInfoE loc_15 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_16 (use{void*} (LocInfoE loc_17 ("p"))))) ;
        "t" <-{ it_layout u8 }
          LocInfoE loc_7 (UnOp (CastOp $ IntOp u8) (IntOp uintptr_t) (LocInfoE loc_7 ((LocInfoE loc_8 (use{it_layout uintptr_t} (LocInfoE loc_9 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_10 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_10 ((LocInfoE loc_11 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_12 (i2v 3 i32))))))))) ;
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
          LocInfoE loc_49 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_50 (use{void*} (LocInfoE loc_51 ("p"))))) ;
        "new_i" <-{ it_layout uintptr_t }
          LocInfoE loc_35 ((LocInfoE loc_36 ((LocInfoE loc_37 (use{it_layout uintptr_t} (LocInfoE loc_38 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_39 ((LocInfoE loc_40 (use{it_layout uintptr_t} (LocInfoE loc_41 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_42 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_42 ((LocInfoE loc_43 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_44 (i2v 3 i32)))))))))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_45 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_45 (use{it_layout u8} (LocInfoE loc_46 ("t"))))))) ;
        "q" <-{ void* }
          LocInfoE loc_28 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_31 (use{it_layout uintptr_t} (LocInfoE loc_32 ("new_i")))) (LocInfoE loc_29 (use{void*} (LocInfoE loc_30 ("p"))))) ;
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 (use{void*} (LocInfoE loc_27 ("q"))))
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
        locinfo: loc_56 ;
        Return (LocInfoE loc_57 (Call (LocInfoE loc_59 (global_tag)) [@{expr} LocInfoE loc_60 (use{void*} (LocInfoE loc_61 ("p"))) ;
               LocInfoE loc_62 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_62 (i2v 0 i32))) ]))
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
          LocInfoE loc_79 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_80 (use{void*} (LocInfoE loc_81 ("p"))))) ;
        locinfo: loc_66 ;
        Return (LocInfoE loc_67 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_70 ((LocInfoE loc_71 (use{it_layout uintptr_t} (LocInfoE loc_72 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_73 ((LocInfoE loc_74 (use{it_layout uintptr_t} (LocInfoE loc_75 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_76 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_78 (i2v 3 i32)))))))))) (LocInfoE loc_68 (use{void*} (LocInfoE loc_69 ("p"))))))
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
          LocInfoE loc_118 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_118 (i2v 0 i32))) ;
        "tp" <-{ void* }
          LocInfoE loc_110 (Call (LocInfoE loc_112 (global_tag)) [@{expr} LocInfoE loc_113 (&(LocInfoE loc_114 ("x"))) ;
          LocInfoE loc_115 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_115 (i2v 1 i32))) ]) ;
        locinfo: loc_88 ;
        assert: (LocInfoE loc_103 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_103 ((LocInfoE loc_104 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_104 (Call (LocInfoE loc_106 (global_tag_of)) [@{expr} LocInfoE loc_107 (use{void*} (LocInfoE loc_108 ("tp"))) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_109 (i2v 1 i32)))))) ;
        "px" <-{ void* }
          LocInfoE loc_95 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_96 (Call (LocInfoE loc_98 (global_untag)) [@{expr} LocInfoE loc_99 (use{void*} (LocInfoE loc_100 ("tp"))) ]))) ;
        locinfo: loc_90 ;
        Return (LocInfoE loc_91 (use{it_layout size_t} (LocInfoE loc_93 (!{void*} (LocInfoE loc_94 ("px"))))))
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
          LocInfoE loc_133 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_134 (use{void*} (LocInfoE loc_135 ("p"))))) ;
        locinfo: loc_124 ;
        Return (LocInfoE loc_125 ((LocInfoE loc_126 ((LocInfoE loc_127 (use{it_layout uintptr_t} (LocInfoE loc_128 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_129 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_129 ((LocInfoE loc_130 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_131 (i2v 3 i32)))))))) ={IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_132 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_132 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.
End code.
