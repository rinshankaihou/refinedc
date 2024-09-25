From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t07_arrays.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t07_arrays.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 14 2 14 16.
  Definition loc_12 : location_info := LocationInfo file_1 15 2 15 16.
  Definition loc_13 : location_info := LocationInfo file_1 16 2 16 12.
  Definition loc_14 : location_info := LocationInfo file_1 16 2 16 7.
  Definition loc_15 : location_info := LocationInfo file_1 16 2 16 7.
  Definition loc_16 : location_info := LocationInfo file_1 16 2 16 4.
  Definition loc_17 : location_info := LocationInfo file_1 16 2 16 4.
  Definition loc_18 : location_info := LocationInfo file_1 16 5 16 6.
  Definition loc_19 : location_info := LocationInfo file_1 16 5 16 6.
  Definition loc_20 : location_info := LocationInfo file_1 16 10 16 11.
  Definition loc_21 : location_info := LocationInfo file_1 16 10 16 11.
  Definition loc_22 : location_info := LocationInfo file_1 15 2 15 7.
  Definition loc_23 : location_info := LocationInfo file_1 15 2 15 7.
  Definition loc_24 : location_info := LocationInfo file_1 15 2 15 4.
  Definition loc_25 : location_info := LocationInfo file_1 15 2 15 4.
  Definition loc_26 : location_info := LocationInfo file_1 15 5 15 6.
  Definition loc_27 : location_info := LocationInfo file_1 15 5 15 6.
  Definition loc_28 : location_info := LocationInfo file_1 15 10 15 15.
  Definition loc_29 : location_info := LocationInfo file_1 15 10 15 15.
  Definition loc_30 : location_info := LocationInfo file_1 15 10 15 15.
  Definition loc_31 : location_info := LocationInfo file_1 15 10 15 12.
  Definition loc_32 : location_info := LocationInfo file_1 15 10 15 12.
  Definition loc_33 : location_info := LocationInfo file_1 15 13 15 14.
  Definition loc_34 : location_info := LocationInfo file_1 15 13 15 14.
  Definition loc_35 : location_info := LocationInfo file_1 14 10 14 15.
  Definition loc_36 : location_info := LocationInfo file_1 14 10 14 15.
  Definition loc_37 : location_info := LocationInfo file_1 14 10 14 15.
  Definition loc_38 : location_info := LocationInfo file_1 14 10 14 12.
  Definition loc_39 : location_info := LocationInfo file_1 14 10 14 12.
  Definition loc_40 : location_info := LocationInfo file_1 14 13 14 14.
  Definition loc_41 : location_info := LocationInfo file_1 14 13 14 14.
  Definition loc_46 : location_info := LocationInfo file_1 24 2 24 20.
  Definition loc_47 : location_info := LocationInfo file_1 25 2 25 20.
  Definition loc_48 : location_info := LocationInfo file_1 25 2 25 9.
  Definition loc_49 : location_info := LocationInfo file_1 25 2 25 9.
  Definition loc_50 : location_info := LocationInfo file_1 25 10 25 12.
  Definition loc_51 : location_info := LocationInfo file_1 25 10 25 12.
  Definition loc_52 : location_info := LocationInfo file_1 25 14 25 15.
  Definition loc_53 : location_info := LocationInfo file_1 25 17 25 18.
  Definition loc_54 : location_info := LocationInfo file_1 24 2 24 9.
  Definition loc_55 : location_info := LocationInfo file_1 24 2 24 9.
  Definition loc_56 : location_info := LocationInfo file_1 24 10 24 12.
  Definition loc_57 : location_info := LocationInfo file_1 24 10 24 12.
  Definition loc_58 : location_info := LocationInfo file_1 24 14 24 15.
  Definition loc_59 : location_info := LocationInfo file_1 24 17 24 18.
  Definition loc_62 : location_info := LocationInfo file_1 42 2 42 23.
  Definition loc_63 : location_info := LocationInfo file_1 44 2 44 14.
  Definition loc_64 : location_info := LocationInfo file_1 53 2 55 3.
  Definition loc_65 : location_info := LocationInfo file_1 53 2 55 3.
  Definition loc_66 : location_info := LocationInfo file_1 53 2 55 3.
  Definition loc_67 : location_info := LocationInfo file_1 57 2 57 13.
  Definition loc_68 : location_info := LocationInfo file_1 57 9 57 12.
  Definition loc_69 : location_info := LocationInfo file_1 57 9 57 12.
  Definition loc_70 : location_info := LocationInfo file_1 53 28 55 3.
  Definition loc_71 : location_info := LocationInfo file_1 54 4 54 32.
  Definition loc_72 : location_info := LocationInfo file_1 53 2 55 3.
  Definition loc_74 : location_info := LocationInfo file_1 53 24 53 25.
  Definition loc_75 : location_info := LocationInfo file_1 54 24 54 32.
  Definition loc_76 : location_info := LocationInfo file_1 54 24 54 27.
  Definition loc_77 : location_info := LocationInfo file_1 54 30 54 31.
  Definition loc_78 : location_info := LocationInfo file_1 54 30 54 31.
  Definition loc_79 : location_info := LocationInfo file_1 54 4 54 32.
  Definition loc_80 : location_info := LocationInfo file_1 54 7 54 22.
  Definition loc_81 : location_info := LocationInfo file_1 54 7 54 12.
  Definition loc_82 : location_info := LocationInfo file_1 54 7 54 12.
  Definition loc_83 : location_info := LocationInfo file_1 54 7 54 12.
  Definition loc_84 : location_info := LocationInfo file_1 54 7 54 9.
  Definition loc_85 : location_info := LocationInfo file_1 54 7 54 9.
  Definition loc_86 : location_info := LocationInfo file_1 54 10 54 11.
  Definition loc_87 : location_info := LocationInfo file_1 54 10 54 11.
  Definition loc_88 : location_info := LocationInfo file_1 54 15 54 22.
  Definition loc_89 : location_info := LocationInfo file_1 54 15 54 22.
  Definition loc_90 : location_info := LocationInfo file_1 54 15 54 22.
  Definition loc_91 : location_info := LocationInfo file_1 54 15 54 17.
  Definition loc_92 : location_info := LocationInfo file_1 54 15 54 17.
  Definition loc_93 : location_info := LocationInfo file_1 54 18 54 21.
  Definition loc_94 : location_info := LocationInfo file_1 54 18 54 21.
  Definition loc_95 : location_info := LocationInfo file_1 53 17 53 22.
  Definition loc_96 : location_info := LocationInfo file_1 53 17 53 18.
  Definition loc_97 : location_info := LocationInfo file_1 53 17 53 18.
  Definition loc_98 : location_info := LocationInfo file_1 53 21 53 22.
  Definition loc_99 : location_info := LocationInfo file_1 53 21 53 22.
  Definition loc_100 : location_info := LocationInfo file_1 53 14 53 15.
  Definition loc_103 : location_info := LocationInfo file_1 44 12 44 13.
  Definition loc_106 : location_info := LocationInfo file_1 42 13 42 23.
  Definition loc_107 : location_info := LocationInfo file_1 42 20 42 22.
  Definition loc_108 : location_info := LocationInfo file_1 42 21 42 22.
  Definition loc_109 : location_info := LocationInfo file_1 42 2 42 23.
  Definition loc_110 : location_info := LocationInfo file_1 42 5 42 11.
  Definition loc_111 : location_info := LocationInfo file_1 42 5 42 6.
  Definition loc_112 : location_info := LocationInfo file_1 42 5 42 6.
  Definition loc_113 : location_info := LocationInfo file_1 42 10 42 11.

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

  (* Definition of function [permute]. *)
  Definition impl_permute : function := {|
    f_args := [
      ("ar", void*);
      ("i", it_layout i32);
      ("j", it_layout i32)
    ];
    f_local_vars := [
      ("k", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "k" <-{ IntOp i32 }
          LocInfoE loc_35 (use{IntOp i32} (LocInfoE loc_37 ((LocInfoE loc_38 (!{PtrOp} (LocInfoE loc_39 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_40 (use{IntOp i32} (LocInfoE loc_41 ("i"))))))) ;
        locinfo: loc_12 ;
        LocInfoE loc_23 ((LocInfoE loc_24 (!{PtrOp} (LocInfoE loc_25 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_26 (use{IntOp i32} (LocInfoE loc_27 ("i"))))) <-{ IntOp i32 }
          LocInfoE loc_28 (use{IntOp i32} (LocInfoE loc_30 ((LocInfoE loc_31 (!{PtrOp} (LocInfoE loc_32 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_33 (use{IntOp i32} (LocInfoE loc_34 ("j"))))))) ;
        locinfo: loc_13 ;
        LocInfoE loc_15 ((LocInfoE loc_16 (!{PtrOp} (LocInfoE loc_17 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_18 (use{IntOp i32} (LocInfoE loc_19 ("j"))))) <-{ IntOp i32 }
          LocInfoE loc_20 (use{IntOp i32} (LocInfoE loc_21 ("k"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [use_permute]. *)
  Definition impl_use_permute (global_permute : loc): function := {|
    f_args := [
      ("ar", void*);
      ("n", it_layout i32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_46 ;
        expr: (LocInfoE loc_46 (Call (LocInfoE loc_55 (global_permute)) [@{expr} LocInfoE loc_56 (use{PtrOp} (LocInfoE loc_57 ("ar"))) ;
        LocInfoE loc_58 (i2v 1 i32) ;
        LocInfoE loc_59 (i2v 2 i32) ])) ;
        locinfo: loc_47 ;
        expr: (LocInfoE loc_47 (Call (LocInfoE loc_49 (global_permute)) [@{expr} LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("ar"))) ;
        LocInfoE loc_52 (i2v 1 i32) ;
        LocInfoE loc_53 (i2v 2 i32) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_array]. *)
  Definition impl_min_array : function := {|
    f_args := [
      ("ar", void*);
      ("n", it_layout i32)
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("res", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_110 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_110 ((LocInfoE loc_111 (use{IntOp i32} (LocInfoE loc_112 ("n")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_113 (i2v 0 i32)))
        then
        locinfo: loc_106 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#1" :=
        "res" <-{ IntOp i32 } LocInfoE loc_103 (i2v 0 i32) ;
        "i" <-{ IntOp i32 } LocInfoE loc_100 (i2v 1 i32) ;
        locinfo: loc_66 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_95 ;
        if{IntOp i32, None}: LocInfoE loc_95 ((LocInfoE loc_96 (use{IntOp i32} (LocInfoE loc_97 ("i")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_98 (use{IntOp i32} (LocInfoE loc_99 ("n")))))
        then
        locinfo: loc_80 ;
          Goto "#3"
        else
        locinfo: loc_67 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_80 ;
        if{IntOp i32, Some "#5"}: LocInfoE loc_80 ((LocInfoE loc_81 (use{IntOp i32} (LocInfoE loc_83 ((LocInfoE loc_84 (!{PtrOp} (LocInfoE loc_85 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_86 (use{IntOp i32} (LocInfoE loc_87 ("i")))))))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_88 (use{IntOp i32} (LocInfoE loc_90 ((LocInfoE loc_91 (!{PtrOp} (LocInfoE loc_92 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_93 (use{IntOp i32} (LocInfoE loc_94 ("res")))))))))
        then
        locinfo: loc_75 ;
          Goto "#6"
        else
        locinfo: loc_72 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_67 ;
        Return (LocInfoE loc_68 (use{IntOp i32} (LocInfoE loc_69 ("res"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_72 ;
        Goto "__cerb_continue0"
      ]> $
      <[ "#6" :=
        locinfo: loc_75 ;
        LocInfoE loc_76 ("res") <-{ IntOp i32 }
          LocInfoE loc_77 (use{IntOp i32} (LocInfoE loc_78 ("i"))) ;
        locinfo: loc_72 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_72 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_106 ;
        Return (LocInfoE loc_107 (UnOp NegOp (IntOp i32) (LocInfoE loc_108 (i2v 1 i32))))
      ]> $
      <[ "#9" :=
        Goto "#1"
      ]> $
      <[ "__cerb_continue0" :=
        LocInfoE loc_74 ("i") <-{ IntOp i32 }
          (use{IntOp i32} (LocInfoE loc_74 ("i"))) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
        locinfo: loc_66 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
