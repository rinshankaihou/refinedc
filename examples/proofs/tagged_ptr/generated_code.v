From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section code.
  Definition file_0 : string := "examples/tagged_ptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 19 2 19 36.
  Definition loc_3 : location_info := LocationInfo file_0 19 9 19 35.
  Definition loc_4 : location_info := LocationInfo file_0 19 9 19 24.
  Definition loc_5 : location_info := LocationInfo file_0 19 22 19 23.
  Definition loc_6 : location_info := LocationInfo file_0 19 22 19 23.
  Definition loc_7 : location_info := LocationInfo file_0 19 27 19 35.
  Definition loc_8 : location_info := LocationInfo file_0 19 28 19 29.
  Definition loc_9 : location_info := LocationInfo file_0 19 33 19 34.
  Definition loc_12 : location_info := LocationInfo file_0 28 2 28 26.
  Definition loc_13 : location_info := LocationInfo file_0 29 2 29 164.
  Definition loc_14 : location_info := LocationInfo file_0 29 9 29 163.
  Definition loc_15 : location_info := LocationInfo file_0 29 35 29 38.
  Definition loc_16 : location_info := LocationInfo file_0 29 35 29 38.
  Definition loc_17 : location_info := LocationInfo file_0 29 40 29 67.
  Definition loc_18 : location_info := LocationInfo file_0 29 41 29 62.
  Definition loc_19 : location_info := LocationInfo file_0 29 41 29 54.
  Definition loc_20 : location_info := LocationInfo file_0 29 53 29 54.
  Definition loc_21 : location_info := LocationInfo file_0 29 53 29 54.
  Definition loc_22 : location_info := LocationInfo file_0 29 57 29 62.
  Definition loc_23 : location_info := LocationInfo file_0 29 57 29 62.
  Definition loc_24 : location_info := LocationInfo file_0 29 65 29 66.
  Definition loc_25 : location_info := LocationInfo file_0 29 65 29 66.
  Definition loc_26 : location_info := LocationInfo file_0 28 16 28 25.
  Definition loc_27 : location_info := LocationInfo file_0 28 16 28 22.
  Definition loc_28 : location_info := LocationInfo file_0 28 16 28 22.
  Definition loc_29 : location_info := LocationInfo file_0 28 23 28 24.
  Definition loc_30 : location_info := LocationInfo file_0 28 23 28 24.
  Definition loc_35 : location_info := LocationInfo file_0 38 2 38 19.
  Definition loc_36 : location_info := LocationInfo file_0 38 9 38 18.
  Definition loc_37 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_38 : location_info := LocationInfo file_0 38 9 38 12.
  Definition loc_39 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_40 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_41 : location_info := LocationInfo file_0 38 16 38 17.
  Definition loc_44 : location_info := LocationInfo file_0 47 2 47 30.
  Definition loc_45 : location_info := LocationInfo file_0 48 2 48 137.
  Definition loc_46 : location_info := LocationInfo file_0 48 9 48 136.
  Definition loc_47 : location_info := LocationInfo file_0 48 35 48 38.
  Definition loc_48 : location_info := LocationInfo file_0 48 35 48 38.
  Definition loc_49 : location_info := LocationInfo file_0 48 40 48 58.
  Definition loc_50 : location_info := LocationInfo file_0 48 41 48 42.
  Definition loc_51 : location_info := LocationInfo file_0 48 41 48 42.
  Definition loc_52 : location_info := LocationInfo file_0 48 45 48 57.
  Definition loc_53 : location_info := LocationInfo file_0 48 45 48 46.
  Definition loc_54 : location_info := LocationInfo file_0 48 45 48 46.
  Definition loc_55 : location_info := LocationInfo file_0 48 49 48 57.
  Definition loc_56 : location_info := LocationInfo file_0 48 50 48 51.
  Definition loc_57 : location_info := LocationInfo file_0 48 55 48 56.
  Definition loc_58 : location_info := LocationInfo file_0 47 16 47 29.
  Definition loc_59 : location_info := LocationInfo file_0 47 28 47 29.
  Definition loc_60 : location_info := LocationInfo file_0 47 28 47 29.
  Definition loc_65 : location_info := LocationInfo file_0 53 2 53 15.
  Definition loc_66 : location_info := LocationInfo file_0 55 2 55 24.
  Definition loc_67 : location_info := LocationInfo file_0 56 2 56 26.
  Definition loc_68 : location_info := LocationInfo file_0 58 2 58 36.
  Definition loc_69 : location_info := LocationInfo file_0 59 2 59 13.
  Definition loc_70 : location_info := LocationInfo file_0 59 9 59 12.
  Definition loc_71 : location_info := LocationInfo file_0 59 9 59 12.
  Definition loc_72 : location_info := LocationInfo file_0 59 10 59 12.
  Definition loc_73 : location_info := LocationInfo file_0 59 10 59 12.
  Definition loc_74 : location_info := LocationInfo file_0 58 15 58 35.
  Definition loc_75 : location_info := LocationInfo file_0 58 26 58 35.
  Definition loc_76 : location_info := LocationInfo file_0 58 26 58 31.
  Definition loc_77 : location_info := LocationInfo file_0 58 26 58 31.
  Definition loc_78 : location_info := LocationInfo file_0 58 32 58 34.
  Definition loc_79 : location_info := LocationInfo file_0 58 32 58 34.
  Definition loc_82 : location_info := LocationInfo file_0 56 9 56 24.
  Definition loc_83 : location_info := LocationInfo file_0 56 9 56 19.
  Definition loc_84 : location_info := LocationInfo file_0 56 9 56 15.
  Definition loc_85 : location_info := LocationInfo file_0 56 9 56 15.
  Definition loc_86 : location_info := LocationInfo file_0 56 16 56 18.
  Definition loc_87 : location_info := LocationInfo file_0 56 16 56 18.
  Definition loc_88 : location_info := LocationInfo file_0 56 23 56 24.
  Definition loc_89 : location_info := LocationInfo file_0 55 13 55 23.
  Definition loc_90 : location_info := LocationInfo file_0 55 13 55 16.
  Definition loc_91 : location_info := LocationInfo file_0 55 13 55 16.
  Definition loc_92 : location_info := LocationInfo file_0 55 17 55 19.
  Definition loc_93 : location_info := LocationInfo file_0 55 18 55 19.
  Definition loc_94 : location_info := LocationInfo file_0 55 21 55 22.
  Definition loc_97 : location_info := LocationInfo file_0 53 13 53 14.
  Definition loc_102 : location_info := LocationInfo file_0 68 2 68 30.
  Definition loc_103 : location_info := LocationInfo file_0 69 2 69 27.
  Definition loc_104 : location_info := LocationInfo file_0 69 9 69 26.
  Definition loc_105 : location_info := LocationInfo file_0 69 9 69 21.
  Definition loc_106 : location_info := LocationInfo file_0 69 9 69 10.
  Definition loc_107 : location_info := LocationInfo file_0 69 9 69 10.
  Definition loc_108 : location_info := LocationInfo file_0 69 13 69 21.
  Definition loc_109 : location_info := LocationInfo file_0 69 14 69 15.
  Definition loc_110 : location_info := LocationInfo file_0 69 19 69 20.
  Definition loc_111 : location_info := LocationInfo file_0 69 25 69 26.
  Definition loc_112 : location_info := LocationInfo file_0 68 16 68 29.
  Definition loc_113 : location_info := LocationInfo file_0 68 28 68 29.
  Definition loc_114 : location_info := LocationInfo file_0 68 28 68 29.

  (* Definition of function [tag_of]. *)
  Definition impl_tag_of : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (UnOp (CastOp $ IntOp u8) (IntOp uintptr_t) (LocInfoE loc_3 ((LocInfoE loc_4 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_5 (use{void*} (LocInfoE loc_6 ("p")))))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_7 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_7 ((LocInfoE loc_8 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_9 (i2v 3 i32))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [tag]. *)
  Definition impl_tag (global_tag_of : loc): function := {|
    f_args := [
      ("p", void*);
      ("t", it_layout u8)
    ];
    f_local_vars := [
      ("old_t", it_layout u8)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "old_t" <-{ it_layout u8 }
          LocInfoE loc_26 (Call (LocInfoE loc_28 (global_tag_of)) [@{expr} LocInfoE loc_29 (use{void*} (LocInfoE loc_30 ("p"))) ]) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_17 ((LocInfoE loc_18 ((LocInfoE loc_19 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_20 (use{void*} (LocInfoE loc_21 ("p")))))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_22 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_22 (use{it_layout u8} (LocInfoE loc_23 ("old_t")))))))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_24 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_24 (use{it_layout u8} (LocInfoE loc_25 ("t")))))))) (LocInfoE loc_15 (use{void*} (LocInfoE loc_16 ("p"))))))
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
        locinfo: loc_35 ;
        Return (LocInfoE loc_36 (Call (LocInfoE loc_38 (global_tag)) [@{expr} LocInfoE loc_39 (use{void*} (LocInfoE loc_40 ("p"))) ;
               LocInfoE loc_41 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_41 (i2v 0 i32))) ]))
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
          LocInfoE loc_58 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_59 (use{void*} (LocInfoE loc_60 ("p"))))) ;
        locinfo: loc_45 ;
        Return (LocInfoE loc_46 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_49 ((LocInfoE loc_50 (use{it_layout uintptr_t} (LocInfoE loc_51 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_52 ((LocInfoE loc_53 (use{it_layout uintptr_t} (LocInfoE loc_54 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_55 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_55 ((LocInfoE loc_56 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_57 (i2v 3 i32)))))))))) (LocInfoE loc_47 (use{void*} (LocInfoE loc_48 ("p"))))))
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
          LocInfoE loc_97 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_97 (i2v 0 i32))) ;
        "tp" <-{ void* }
          LocInfoE loc_89 (Call (LocInfoE loc_91 (global_tag)) [@{expr} LocInfoE loc_92 (&(LocInfoE loc_93 ("x"))) ;
          LocInfoE loc_94 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_94 (i2v 1 i32))) ]) ;
        locinfo: loc_67 ;
        assert: (LocInfoE loc_82 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_82 ((LocInfoE loc_83 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_83 (Call (LocInfoE loc_85 (global_tag_of)) [@{expr} LocInfoE loc_86 (use{void*} (LocInfoE loc_87 ("tp"))) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_88 (i2v 1 i32)))))) ;
        "px" <-{ void* }
          LocInfoE loc_74 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_75 (Call (LocInfoE loc_77 (global_untag)) [@{expr} LocInfoE loc_78 (use{void*} (LocInfoE loc_79 ("tp"))) ]))) ;
        locinfo: loc_69 ;
        Return (LocInfoE loc_70 (use{it_layout size_t} (LocInfoE loc_72 (!{void*} (LocInfoE loc_73 ("px"))))))
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
          LocInfoE loc_112 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_113 (use{void*} (LocInfoE loc_114 ("p"))))) ;
        locinfo: loc_103 ;
        Return (LocInfoE loc_104 ((LocInfoE loc_105 ((LocInfoE loc_106 (use{it_layout uintptr_t} (LocInfoE loc_107 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_108 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_108 ((LocInfoE loc_109 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_110 (i2v 3 i32)))))))) ={IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_111 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_111 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.
End code.
