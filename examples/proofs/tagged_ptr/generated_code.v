From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section code.
  Definition file_0 : string := "examples/tagged_ptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 20 2 20 36.
  Definition loc_3 : location_info := LocationInfo file_0 20 9 20 35.
  Definition loc_4 : location_info := LocationInfo file_0 20 9 20 24.
  Definition loc_5 : location_info := LocationInfo file_0 20 22 20 23.
  Definition loc_6 : location_info := LocationInfo file_0 20 22 20 23.
  Definition loc_7 : location_info := LocationInfo file_0 20 27 20 35.
  Definition loc_8 : location_info := LocationInfo file_0 20 28 20 29.
  Definition loc_9 : location_info := LocationInfo file_0 20 33 20 34.
  Definition loc_12 : location_info := LocationInfo file_0 29 2 29 26.
  Definition loc_13 : location_info := LocationInfo file_0 30 2 30 139.
  Definition loc_14 : location_info := LocationInfo file_0 30 9 30 138.
  Definition loc_15 : location_info := LocationInfo file_0 30 35 30 38.
  Definition loc_16 : location_info := LocationInfo file_0 30 35 30 38.
  Definition loc_17 : location_info := LocationInfo file_0 30 40 30 77.
  Definition loc_18 : location_info := LocationInfo file_0 30 49 30 76.
  Definition loc_19 : location_info := LocationInfo file_0 30 50 30 71.
  Definition loc_20 : location_info := LocationInfo file_0 30 50 30 63.
  Definition loc_21 : location_info := LocationInfo file_0 30 62 30 63.
  Definition loc_22 : location_info := LocationInfo file_0 30 62 30 63.
  Definition loc_23 : location_info := LocationInfo file_0 30 66 30 71.
  Definition loc_24 : location_info := LocationInfo file_0 30 66 30 71.
  Definition loc_25 : location_info := LocationInfo file_0 30 74 30 75.
  Definition loc_26 : location_info := LocationInfo file_0 30 74 30 75.
  Definition loc_27 : location_info := LocationInfo file_0 29 16 29 25.
  Definition loc_28 : location_info := LocationInfo file_0 29 16 29 22.
  Definition loc_29 : location_info := LocationInfo file_0 29 16 29 22.
  Definition loc_30 : location_info := LocationInfo file_0 29 23 29 24.
  Definition loc_31 : location_info := LocationInfo file_0 29 23 29 24.
  Definition loc_36 : location_info := LocationInfo file_0 39 2 39 19.
  Definition loc_37 : location_info := LocationInfo file_0 39 9 39 18.
  Definition loc_38 : location_info := LocationInfo file_0 39 9 39 12.
  Definition loc_39 : location_info := LocationInfo file_0 39 9 39 12.
  Definition loc_40 : location_info := LocationInfo file_0 39 13 39 14.
  Definition loc_41 : location_info := LocationInfo file_0 39 13 39 14.
  Definition loc_42 : location_info := LocationInfo file_0 39 16 39 17.
  Definition loc_45 : location_info := LocationInfo file_0 48 2 48 30.
  Definition loc_46 : location_info := LocationInfo file_0 49 2 49 121.
  Definition loc_47 : location_info := LocationInfo file_0 49 9 49 120.
  Definition loc_48 : location_info := LocationInfo file_0 49 35 49 38.
  Definition loc_49 : location_info := LocationInfo file_0 49 35 49 38.
  Definition loc_50 : location_info := LocationInfo file_0 49 40 49 68.
  Definition loc_51 : location_info := LocationInfo file_0 49 49 49 67.
  Definition loc_52 : location_info := LocationInfo file_0 49 50 49 51.
  Definition loc_53 : location_info := LocationInfo file_0 49 50 49 51.
  Definition loc_54 : location_info := LocationInfo file_0 49 54 49 66.
  Definition loc_55 : location_info := LocationInfo file_0 49 54 49 55.
  Definition loc_56 : location_info := LocationInfo file_0 49 54 49 55.
  Definition loc_57 : location_info := LocationInfo file_0 49 58 49 66.
  Definition loc_58 : location_info := LocationInfo file_0 49 59 49 60.
  Definition loc_59 : location_info := LocationInfo file_0 49 64 49 65.
  Definition loc_60 : location_info := LocationInfo file_0 48 16 48 29.
  Definition loc_61 : location_info := LocationInfo file_0 48 28 48 29.
  Definition loc_62 : location_info := LocationInfo file_0 48 28 48 29.
  Definition loc_67 : location_info := LocationInfo file_0 54 2 54 15.
  Definition loc_68 : location_info := LocationInfo file_0 56 2 56 24.
  Definition loc_69 : location_info := LocationInfo file_0 57 2 57 26.
  Definition loc_70 : location_info := LocationInfo file_0 59 2 59 36.
  Definition loc_71 : location_info := LocationInfo file_0 60 2 60 13.
  Definition loc_72 : location_info := LocationInfo file_0 60 9 60 12.
  Definition loc_73 : location_info := LocationInfo file_0 60 9 60 12.
  Definition loc_74 : location_info := LocationInfo file_0 60 10 60 12.
  Definition loc_75 : location_info := LocationInfo file_0 60 10 60 12.
  Definition loc_76 : location_info := LocationInfo file_0 59 15 59 35.
  Definition loc_77 : location_info := LocationInfo file_0 59 26 59 35.
  Definition loc_78 : location_info := LocationInfo file_0 59 26 59 31.
  Definition loc_79 : location_info := LocationInfo file_0 59 26 59 31.
  Definition loc_80 : location_info := LocationInfo file_0 59 32 59 34.
  Definition loc_81 : location_info := LocationInfo file_0 59 32 59 34.
  Definition loc_84 : location_info := LocationInfo file_0 57 9 57 24.
  Definition loc_85 : location_info := LocationInfo file_0 57 9 57 19.
  Definition loc_86 : location_info := LocationInfo file_0 57 9 57 15.
  Definition loc_87 : location_info := LocationInfo file_0 57 9 57 15.
  Definition loc_88 : location_info := LocationInfo file_0 57 16 57 18.
  Definition loc_89 : location_info := LocationInfo file_0 57 16 57 18.
  Definition loc_90 : location_info := LocationInfo file_0 57 23 57 24.
  Definition loc_91 : location_info := LocationInfo file_0 56 13 56 23.
  Definition loc_92 : location_info := LocationInfo file_0 56 13 56 16.
  Definition loc_93 : location_info := LocationInfo file_0 56 13 56 16.
  Definition loc_94 : location_info := LocationInfo file_0 56 17 56 19.
  Definition loc_95 : location_info := LocationInfo file_0 56 18 56 19.
  Definition loc_96 : location_info := LocationInfo file_0 56 21 56 22.
  Definition loc_99 : location_info := LocationInfo file_0 54 13 54 14.
  Definition loc_104 : location_info := LocationInfo file_0 69 2 69 30.
  Definition loc_105 : location_info := LocationInfo file_0 70 2 70 27.
  Definition loc_106 : location_info := LocationInfo file_0 70 9 70 26.
  Definition loc_107 : location_info := LocationInfo file_0 70 9 70 21.
  Definition loc_108 : location_info := LocationInfo file_0 70 9 70 10.
  Definition loc_109 : location_info := LocationInfo file_0 70 9 70 10.
  Definition loc_110 : location_info := LocationInfo file_0 70 13 70 21.
  Definition loc_111 : location_info := LocationInfo file_0 70 14 70 15.
  Definition loc_112 : location_info := LocationInfo file_0 70 19 70 20.
  Definition loc_113 : location_info := LocationInfo file_0 70 25 70 26.
  Definition loc_114 : location_info := LocationInfo file_0 69 16 69 29.
  Definition loc_115 : location_info := LocationInfo file_0 69 28 69 29.
  Definition loc_116 : location_info := LocationInfo file_0 69 28 69 29.

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
          LocInfoE loc_27 (Call (LocInfoE loc_29 (global_tag_of)) [@{expr} LocInfoE loc_30 (use{void*} (LocInfoE loc_31 ("p"))) ]) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (CopyAllocId (PtrOp) (LocInfoE loc_17 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_18 ((LocInfoE loc_19 ((LocInfoE loc_20 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_21 (use{void*} (LocInfoE loc_22 ("p")))))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_23 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_23 (use{it_layout u8} (LocInfoE loc_24 ("old_t")))))))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_25 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u8) (LocInfoE loc_25 (use{it_layout u8} (LocInfoE loc_26 ("t")))))))))) (LocInfoE loc_15 (use{void*} (LocInfoE loc_16 ("p"))))))
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
        locinfo: loc_36 ;
        Return (LocInfoE loc_37 (Call (LocInfoE loc_39 (global_tag)) [@{expr} LocInfoE loc_40 (use{void*} (LocInfoE loc_41 ("p"))) ;
               LocInfoE loc_42 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_42 (i2v 0 i32))) ]))
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
          LocInfoE loc_60 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_61 (use{void*} (LocInfoE loc_62 ("p"))))) ;
        locinfo: loc_46 ;
        Return (LocInfoE loc_47 (CopyAllocId (PtrOp) (LocInfoE loc_50 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_51 ((LocInfoE loc_52 (use{it_layout uintptr_t} (LocInfoE loc_53 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_54 ((LocInfoE loc_55 (use{it_layout uintptr_t} (LocInfoE loc_56 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_57 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_57 ((LocInfoE loc_58 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_59 (i2v 3 i32)))))))))))) (LocInfoE loc_48 (use{void*} (LocInfoE loc_49 ("p"))))))
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
          LocInfoE loc_99 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_99 (i2v 0 i32))) ;
        "tp" <-{ void* }
          LocInfoE loc_91 (Call (LocInfoE loc_93 (global_tag)) [@{expr} LocInfoE loc_94 (&(LocInfoE loc_95 ("x"))) ;
          LocInfoE loc_96 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_96 (i2v 1 i32))) ]) ;
        locinfo: loc_69 ;
        assert: (LocInfoE loc_84 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_84 ((LocInfoE loc_85 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_85 (Call (LocInfoE loc_87 (global_tag_of)) [@{expr} LocInfoE loc_88 (use{void*} (LocInfoE loc_89 ("tp"))) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_90 (i2v 1 i32)))))) ;
        "px" <-{ void* }
          LocInfoE loc_76 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_77 (Call (LocInfoE loc_79 (global_untag)) [@{expr} LocInfoE loc_80 (use{void*} (LocInfoE loc_81 ("tp"))) ]))) ;
        locinfo: loc_71 ;
        Return (LocInfoE loc_72 (use{it_layout size_t} (LocInfoE loc_74 (!{void*} (LocInfoE loc_75 ("px"))))))
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
          LocInfoE loc_114 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_115 (use{void*} (LocInfoE loc_116 ("p"))))) ;
        locinfo: loc_105 ;
        Return (LocInfoE loc_106 ((LocInfoE loc_107 ((LocInfoE loc_108 (use{it_layout uintptr_t} (LocInfoE loc_109 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_110 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_110 ((LocInfoE loc_111 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_112 (i2v 3 i32)))))))) ={IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_113 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_113 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.
End code.
