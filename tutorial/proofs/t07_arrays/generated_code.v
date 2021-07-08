From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t07_arrays.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t07_arrays.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
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
  Definition loc_46 : location_info := LocationInfo file_1 33 2 33 23.
  Definition loc_47 : location_info := LocationInfo file_1 35 2 35 14.
  Definition loc_48 : location_info := LocationInfo file_1 44 2 46 3.
  Definition loc_49 : location_info := LocationInfo file_1 44 2 46 3.
  Definition loc_50 : location_info := LocationInfo file_1 44 2 46 3.
  Definition loc_51 : location_info := LocationInfo file_1 48 2 48 13.
  Definition loc_52 : location_info := LocationInfo file_1 48 9 48 12.
  Definition loc_53 : location_info := LocationInfo file_1 48 9 48 12.
  Definition loc_54 : location_info := LocationInfo file_1 44 28 46 3.
  Definition loc_55 : location_info := LocationInfo file_1 45 4 45 32.
  Definition loc_56 : location_info := LocationInfo file_1 44 2 46 3.
  Definition loc_58 : location_info := LocationInfo file_1 44 24 44 25.
  Definition loc_59 : location_info := LocationInfo file_1 45 24 45 32.
  Definition loc_60 : location_info := LocationInfo file_1 45 24 45 27.
  Definition loc_61 : location_info := LocationInfo file_1 45 30 45 31.
  Definition loc_62 : location_info := LocationInfo file_1 45 30 45 31.
  Definition loc_64 : location_info := LocationInfo file_1 45 7 45 22.
  Definition loc_65 : location_info := LocationInfo file_1 45 7 45 12.
  Definition loc_66 : location_info := LocationInfo file_1 45 7 45 12.
  Definition loc_67 : location_info := LocationInfo file_1 45 7 45 12.
  Definition loc_68 : location_info := LocationInfo file_1 45 7 45 9.
  Definition loc_69 : location_info := LocationInfo file_1 45 7 45 9.
  Definition loc_70 : location_info := LocationInfo file_1 45 10 45 11.
  Definition loc_71 : location_info := LocationInfo file_1 45 10 45 11.
  Definition loc_72 : location_info := LocationInfo file_1 45 15 45 22.
  Definition loc_73 : location_info := LocationInfo file_1 45 15 45 22.
  Definition loc_74 : location_info := LocationInfo file_1 45 15 45 22.
  Definition loc_75 : location_info := LocationInfo file_1 45 15 45 17.
  Definition loc_76 : location_info := LocationInfo file_1 45 15 45 17.
  Definition loc_77 : location_info := LocationInfo file_1 45 18 45 21.
  Definition loc_78 : location_info := LocationInfo file_1 45 18 45 21.
  Definition loc_79 : location_info := LocationInfo file_1 44 17 44 22.
  Definition loc_80 : location_info := LocationInfo file_1 44 17 44 18.
  Definition loc_81 : location_info := LocationInfo file_1 44 17 44 18.
  Definition loc_82 : location_info := LocationInfo file_1 44 21 44 22.
  Definition loc_83 : location_info := LocationInfo file_1 44 21 44 22.
  Definition loc_84 : location_info := LocationInfo file_1 44 14 44 15.
  Definition loc_87 : location_info := LocationInfo file_1 35 12 35 13.
  Definition loc_90 : location_info := LocationInfo file_1 33 13 33 23.
  Definition loc_91 : location_info := LocationInfo file_1 33 20 33 22.
  Definition loc_92 : location_info := LocationInfo file_1 33 21 33 22.
  Definition loc_94 : location_info := LocationInfo file_1 33 5 33 11.
  Definition loc_95 : location_info := LocationInfo file_1 33 5 33 6.
  Definition loc_96 : location_info := LocationInfo file_1 33 5 33 6.
  Definition loc_97 : location_info := LocationInfo file_1 33 10 33 11.

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
        "k" <-{ it_layout i32 }
          LocInfoE loc_35 (use{it_layout i32} (LocInfoE loc_37 ((LocInfoE loc_38 (!{void*} (LocInfoE loc_39 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_40 (use{it_layout i32} (LocInfoE loc_41 ("i"))))))) ;
        locinfo: loc_12 ;
        LocInfoE loc_23 ((LocInfoE loc_24 (!{void*} (LocInfoE loc_25 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_26 (use{it_layout i32} (LocInfoE loc_27 ("i"))))) <-{ it_layout i32 }
          LocInfoE loc_28 (use{it_layout i32} (LocInfoE loc_30 ((LocInfoE loc_31 (!{void*} (LocInfoE loc_32 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_33 (use{it_layout i32} (LocInfoE loc_34 ("j"))))))) ;
        locinfo: loc_13 ;
        LocInfoE loc_15 ((LocInfoE loc_16 (!{void*} (LocInfoE loc_17 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_18 (use{it_layout i32} (LocInfoE loc_19 ("j"))))) <-{ it_layout i32 }
          LocInfoE loc_20 (use{it_layout i32} (LocInfoE loc_21 ("k"))) ;
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
        locinfo: loc_94 ;
        if: LocInfoE loc_94 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_94 ((LocInfoE loc_95 (use{it_layout i32} (LocInfoE loc_96 ("n")))) ={IntOp i32, IntOp i32} (LocInfoE loc_97 (i2v 0 i32)))))
        then
        locinfo: loc_90 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#1" :=
        "res" <-{ it_layout i32 } LocInfoE loc_87 (i2v 0 i32) ;
        "i" <-{ it_layout i32 } LocInfoE loc_84 (i2v 1 i32) ;
        locinfo: loc_50 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_79 ;
        if: LocInfoE loc_79 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_79 ((LocInfoE loc_80 (use{it_layout i32} (LocInfoE loc_81 ("i")))) <{IntOp i32, IntOp i32} (LocInfoE loc_82 (use{it_layout i32} (LocInfoE loc_83 ("n")))))))
        then
        locinfo: loc_64 ;
          Goto "#3"
        else
        locinfo: loc_51 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_64 ;
        if: LocInfoE loc_64 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_64 ((LocInfoE loc_65 (use{it_layout i32} (LocInfoE loc_67 ((LocInfoE loc_68 (!{void*} (LocInfoE loc_69 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_70 (use{it_layout i32} (LocInfoE loc_71 ("i")))))))) <{IntOp i32, IntOp i32} (LocInfoE loc_72 (use{it_layout i32} (LocInfoE loc_74 ((LocInfoE loc_75 (!{void*} (LocInfoE loc_76 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_77 (use{it_layout i32} (LocInfoE loc_78 ("res")))))))))))
        then
        locinfo: loc_59 ;
          Goto "#6"
        else
        locinfo: loc_56 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_51 ;
        Return (LocInfoE loc_52 (use{it_layout i32} (LocInfoE loc_53 ("res"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_56 ;
        Goto "continue6"
      ]> $
      <[ "#6" :=
        locinfo: loc_59 ;
        LocInfoE loc_60 ("res") <-{ it_layout i32 }
          LocInfoE loc_61 (use{it_layout i32} (LocInfoE loc_62 ("i"))) ;
        locinfo: loc_56 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_56 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_90 ;
        Return (LocInfoE loc_91 (UnOp NegOp (IntOp i32) (LocInfoE loc_92 (i2v 1 i32))))
      ]> $
      <[ "#9" :=
        Goto "#1"
      ]> $
      <[ "continue6" :=
        LocInfoE loc_58 ("i") <-{ it_layout i32 }
          (use{it_layout i32} (LocInfoE loc_58 ("i"))) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
        locinfo: loc_50 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
