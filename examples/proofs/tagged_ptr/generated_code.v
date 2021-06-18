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
  Definition loc_36 : location_info := LocationInfo file_0 39 2 39 30.
  Definition loc_37 : location_info := LocationInfo file_0 40 2 40 121.
  Definition loc_38 : location_info := LocationInfo file_0 40 9 40 120.
  Definition loc_39 : location_info := LocationInfo file_0 40 35 40 38.
  Definition loc_40 : location_info := LocationInfo file_0 40 35 40 38.
  Definition loc_41 : location_info := LocationInfo file_0 40 40 40 68.
  Definition loc_42 : location_info := LocationInfo file_0 40 49 40 67.
  Definition loc_43 : location_info := LocationInfo file_0 40 50 40 51.
  Definition loc_44 : location_info := LocationInfo file_0 40 50 40 51.
  Definition loc_45 : location_info := LocationInfo file_0 40 54 40 66.
  Definition loc_46 : location_info := LocationInfo file_0 40 54 40 55.
  Definition loc_47 : location_info := LocationInfo file_0 40 54 40 55.
  Definition loc_48 : location_info := LocationInfo file_0 40 58 40 66.
  Definition loc_49 : location_info := LocationInfo file_0 40 59 40 60.
  Definition loc_50 : location_info := LocationInfo file_0 40 64 40 65.
  Definition loc_51 : location_info := LocationInfo file_0 39 16 39 29.
  Definition loc_52 : location_info := LocationInfo file_0 39 28 39 29.
  Definition loc_53 : location_info := LocationInfo file_0 39 28 39 29.
  Definition loc_58 : location_info := LocationInfo file_0 45 2 45 15.
  Definition loc_59 : location_info := LocationInfo file_0 47 2 47 24.
  Definition loc_60 : location_info := LocationInfo file_0 48 2 48 26.
  Definition loc_61 : location_info := LocationInfo file_0 50 2 50 36.
  Definition loc_62 : location_info := LocationInfo file_0 51 2 51 13.
  Definition loc_63 : location_info := LocationInfo file_0 51 9 51 12.
  Definition loc_64 : location_info := LocationInfo file_0 51 9 51 12.
  Definition loc_65 : location_info := LocationInfo file_0 51 10 51 12.
  Definition loc_66 : location_info := LocationInfo file_0 51 10 51 12.
  Definition loc_67 : location_info := LocationInfo file_0 50 15 50 35.
  Definition loc_68 : location_info := LocationInfo file_0 50 26 50 35.
  Definition loc_69 : location_info := LocationInfo file_0 50 26 50 31.
  Definition loc_70 : location_info := LocationInfo file_0 50 26 50 31.
  Definition loc_71 : location_info := LocationInfo file_0 50 32 50 34.
  Definition loc_72 : location_info := LocationInfo file_0 50 32 50 34.
  Definition loc_75 : location_info := LocationInfo file_0 48 9 48 24.
  Definition loc_76 : location_info := LocationInfo file_0 48 9 48 19.
  Definition loc_77 : location_info := LocationInfo file_0 48 9 48 15.
  Definition loc_78 : location_info := LocationInfo file_0 48 9 48 15.
  Definition loc_79 : location_info := LocationInfo file_0 48 16 48 18.
  Definition loc_80 : location_info := LocationInfo file_0 48 16 48 18.
  Definition loc_81 : location_info := LocationInfo file_0 48 23 48 24.
  Definition loc_82 : location_info := LocationInfo file_0 47 13 47 23.
  Definition loc_83 : location_info := LocationInfo file_0 47 13 47 16.
  Definition loc_84 : location_info := LocationInfo file_0 47 13 47 16.
  Definition loc_85 : location_info := LocationInfo file_0 47 17 47 19.
  Definition loc_86 : location_info := LocationInfo file_0 47 18 47 19.
  Definition loc_87 : location_info := LocationInfo file_0 47 21 47 22.
  Definition loc_90 : location_info := LocationInfo file_0 45 13 45 14.
  Definition loc_95 : location_info := LocationInfo file_0 60 2 60 30.
  Definition loc_96 : location_info := LocationInfo file_0 61 2 61 27.
  Definition loc_97 : location_info := LocationInfo file_0 61 9 61 26.
  Definition loc_98 : location_info := LocationInfo file_0 61 9 61 21.
  Definition loc_99 : location_info := LocationInfo file_0 61 9 61 10.
  Definition loc_100 : location_info := LocationInfo file_0 61 9 61 10.
  Definition loc_101 : location_info := LocationInfo file_0 61 13 61 21.
  Definition loc_102 : location_info := LocationInfo file_0 61 14 61 15.
  Definition loc_103 : location_info := LocationInfo file_0 61 19 61 20.
  Definition loc_104 : location_info := LocationInfo file_0 61 25 61 26.
  Definition loc_105 : location_info := LocationInfo file_0 60 16 60 29.
  Definition loc_106 : location_info := LocationInfo file_0 60 28 60 29.
  Definition loc_107 : location_info := LocationInfo file_0 60 28 60 29.

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
  Definition impl_untag : function := {|
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
          LocInfoE loc_51 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_52 (use{void*} (LocInfoE loc_53 ("p"))))) ;
        locinfo: loc_37 ;
        Return (LocInfoE loc_38 (CopyAllocId (PtrOp) (LocInfoE loc_41 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_42 ((LocInfoE loc_43 (use{it_layout uintptr_t} (LocInfoE loc_44 ("i")))) -{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_45 ((LocInfoE loc_46 (use{it_layout uintptr_t} (LocInfoE loc_47 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_48 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_48 ((LocInfoE loc_49 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_50 (i2v 3 i32)))))))))))) (LocInfoE loc_39 (use{void*} (LocInfoE loc_40 ("p"))))))
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
          LocInfoE loc_90 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_90 (i2v 0 i32))) ;
        "tp" <-{ void* }
          LocInfoE loc_82 (Call (LocInfoE loc_84 (global_tag)) [@{expr} LocInfoE loc_85 (&(LocInfoE loc_86 ("x"))) ;
          LocInfoE loc_87 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_87 (i2v 1 i32))) ]) ;
        locinfo: loc_60 ;
        assert: (LocInfoE loc_75 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_75 ((LocInfoE loc_76 (UnOp (CastOp $ IntOp i32) (IntOp u8) (LocInfoE loc_76 (Call (LocInfoE loc_78 (global_tag_of)) [@{expr} LocInfoE loc_79 (use{void*} (LocInfoE loc_80 ("tp"))) ])))) ={IntOp i32, IntOp i32} (LocInfoE loc_81 (i2v 1 i32)))))) ;
        "px" <-{ void* }
          LocInfoE loc_67 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_68 (Call (LocInfoE loc_70 (global_untag)) [@{expr} LocInfoE loc_71 (use{void*} (LocInfoE loc_72 ("tp"))) ]))) ;
        locinfo: loc_62 ;
        Return (LocInfoE loc_63 (use{it_layout size_t} (LocInfoE loc_65 (!{void*} (LocInfoE loc_66 ("px"))))))
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
          LocInfoE loc_105 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_106 (use{void*} (LocInfoE loc_107 ("p"))))) ;
        locinfo: loc_96 ;
        Return (LocInfoE loc_97 ((LocInfoE loc_98 ((LocInfoE loc_99 (use{it_layout uintptr_t} (LocInfoE loc_100 ("i")))) %{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_101 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_101 ((LocInfoE loc_102 (i2v 1 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_103 (i2v 3 i32)))))))) ={IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_104 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_104 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.
End code.
