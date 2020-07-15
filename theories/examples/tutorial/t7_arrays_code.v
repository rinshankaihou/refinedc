From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t7_arrays.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/t7_arrays.c".
  Definition loc_2 : location_info := LocationInfo file_0 14 2 14 16.
  Definition loc_3 : location_info := LocationInfo file_0 15 2 15 16.
  Definition loc_4 : location_info := LocationInfo file_0 16 2 16 12.
  Definition loc_5 : location_info := LocationInfo file_0 16 2 16 7.
  Definition loc_6 : location_info := LocationInfo file_0 16 2 16 7.
  Definition loc_7 : location_info := LocationInfo file_0 16 2 16 4.
  Definition loc_8 : location_info := LocationInfo file_0 16 2 16 4.
  Definition loc_9 : location_info := LocationInfo file_0 16 5 16 6.
  Definition loc_10 : location_info := LocationInfo file_0 16 5 16 6.
  Definition loc_11 : location_info := LocationInfo file_0 16 10 16 11.
  Definition loc_12 : location_info := LocationInfo file_0 16 10 16 11.
  Definition loc_13 : location_info := LocationInfo file_0 15 2 15 7.
  Definition loc_14 : location_info := LocationInfo file_0 15 2 15 7.
  Definition loc_15 : location_info := LocationInfo file_0 15 2 15 4.
  Definition loc_16 : location_info := LocationInfo file_0 15 2 15 4.
  Definition loc_17 : location_info := LocationInfo file_0 15 5 15 6.
  Definition loc_18 : location_info := LocationInfo file_0 15 5 15 6.
  Definition loc_19 : location_info := LocationInfo file_0 15 10 15 15.
  Definition loc_20 : location_info := LocationInfo file_0 15 10 15 15.
  Definition loc_21 : location_info := LocationInfo file_0 15 10 15 15.
  Definition loc_22 : location_info := LocationInfo file_0 15 10 15 12.
  Definition loc_23 : location_info := LocationInfo file_0 15 10 15 12.
  Definition loc_24 : location_info := LocationInfo file_0 15 13 15 14.
  Definition loc_25 : location_info := LocationInfo file_0 15 13 15 14.
  Definition loc_26 : location_info := LocationInfo file_0 14 10 14 15.
  Definition loc_27 : location_info := LocationInfo file_0 14 10 14 15.
  Definition loc_28 : location_info := LocationInfo file_0 14 10 14 15.
  Definition loc_29 : location_info := LocationInfo file_0 14 10 14 12.
  Definition loc_30 : location_info := LocationInfo file_0 14 10 14 12.
  Definition loc_31 : location_info := LocationInfo file_0 14 13 14 14.
  Definition loc_32 : location_info := LocationInfo file_0 14 13 14 14.
  Definition loc_37 : location_info := LocationInfo file_0 32 2 32 23.
  Definition loc_38 : location_info := LocationInfo file_0 34 2 34 14.
  Definition loc_39 : location_info := LocationInfo file_0 43 2 45 3.
  Definition loc_40 : location_info := LocationInfo file_0 43 2 45 3.
  Definition loc_41 : location_info := LocationInfo file_0 43 2 45 3.
  Definition loc_42 : location_info := LocationInfo file_0 47 2 47 13.
  Definition loc_43 : location_info := LocationInfo file_0 47 9 47 12.
  Definition loc_44 : location_info := LocationInfo file_0 47 9 47 12.
  Definition loc_45 : location_info := LocationInfo file_0 43 28 45 3.
  Definition loc_46 : location_info := LocationInfo file_0 44 4 44 32.
  Definition loc_47 : location_info := LocationInfo file_0 43 2 45 3.
  Definition loc_49 : location_info := LocationInfo file_0 43 24 43 25.
  Definition loc_50 : location_info := LocationInfo file_0 44 24 44 32.
  Definition loc_51 : location_info := LocationInfo file_0 44 24 44 27.
  Definition loc_52 : location_info := LocationInfo file_0 44 30 44 31.
  Definition loc_53 : location_info := LocationInfo file_0 44 30 44 31.
  Definition loc_55 : location_info := LocationInfo file_0 44 7 44 22.
  Definition loc_56 : location_info := LocationInfo file_0 44 7 44 12.
  Definition loc_57 : location_info := LocationInfo file_0 44 7 44 12.
  Definition loc_58 : location_info := LocationInfo file_0 44 7 44 12.
  Definition loc_59 : location_info := LocationInfo file_0 44 7 44 9.
  Definition loc_60 : location_info := LocationInfo file_0 44 7 44 9.
  Definition loc_61 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_62 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_63 : location_info := LocationInfo file_0 44 15 44 22.
  Definition loc_64 : location_info := LocationInfo file_0 44 15 44 22.
  Definition loc_65 : location_info := LocationInfo file_0 44 15 44 22.
  Definition loc_66 : location_info := LocationInfo file_0 44 15 44 17.
  Definition loc_67 : location_info := LocationInfo file_0 44 15 44 17.
  Definition loc_68 : location_info := LocationInfo file_0 44 18 44 21.
  Definition loc_69 : location_info := LocationInfo file_0 44 18 44 21.
  Definition loc_70 : location_info := LocationInfo file_0 43 17 43 22.
  Definition loc_71 : location_info := LocationInfo file_0 43 17 43 18.
  Definition loc_72 : location_info := LocationInfo file_0 43 17 43 18.
  Definition loc_73 : location_info := LocationInfo file_0 43 21 43 22.
  Definition loc_74 : location_info := LocationInfo file_0 43 21 43 22.
  Definition loc_75 : location_info := LocationInfo file_0 43 14 43 15.
  Definition loc_78 : location_info := LocationInfo file_0 34 12 34 13.
  Definition loc_81 : location_info := LocationInfo file_0 32 13 32 23.
  Definition loc_82 : location_info := LocationInfo file_0 32 20 32 22.
  Definition loc_83 : location_info := LocationInfo file_0 32 21 32 22.
  Definition loc_85 : location_info := LocationInfo file_0 32 5 32 11.
  Definition loc_86 : location_info := LocationInfo file_0 32 5 32 6.
  Definition loc_87 : location_info := LocationInfo file_0 32 5 32 6.
  Definition loc_88 : location_info := LocationInfo file_0 32 10 32 11.

  (* Definition of function [permute]. *)
  Definition impl_permute : function := {|
    f_args := [
      ("ar", LPtr);
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
          LocInfoE loc_26 (use{it_layout i32} (LocInfoE loc_28 ((LocInfoE loc_29 (!{LPtr} (LocInfoE loc_30 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_31 (use{it_layout i32} (LocInfoE loc_32 ("i"))))))) ;
        locinfo: loc_3 ;
        LocInfoE loc_14 ((LocInfoE loc_15 (!{LPtr} (LocInfoE loc_16 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_17 (use{it_layout i32} (LocInfoE loc_18 ("i"))))) <-{ it_layout i32 }
          LocInfoE loc_19 (use{it_layout i32} (LocInfoE loc_21 ((LocInfoE loc_22 (!{LPtr} (LocInfoE loc_23 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_24 (use{it_layout i32} (LocInfoE loc_25 ("j"))))))) ;
        locinfo: loc_4 ;
        LocInfoE loc_6 ((LocInfoE loc_7 (!{LPtr} (LocInfoE loc_8 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_9 (use{it_layout i32} (LocInfoE loc_10 ("j"))))) <-{ it_layout i32 }
          LocInfoE loc_11 (use{it_layout i32} (LocInfoE loc_12 ("k"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_array]. *)
  Definition impl_min_array : function := {|
    f_args := [
      ("ar", LPtr);
      ("n", it_layout i32)
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("res", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_85 ;
        if: LocInfoE loc_85 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_85 ((LocInfoE loc_86 (use{it_layout i32} (LocInfoE loc_87 ("n")))) ={IntOp i32, IntOp i32} (LocInfoE loc_88 (i2v 0 i32)))))
        then
        locinfo: loc_81 ;
          Goto "#8"
        else
        Goto "#9"
      ]> $
      <[ "#1" :=
        "res" <-{ it_layout i32 } LocInfoE loc_78 (i2v 0 i32) ;
        "i" <-{ it_layout i32 } LocInfoE loc_75 (i2v 1 i32) ;
        locinfo: loc_41 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_70 ;
        if: LocInfoE loc_70 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_70 ((LocInfoE loc_71 (use{it_layout i32} (LocInfoE loc_72 ("i")))) <{IntOp i32, IntOp i32} (LocInfoE loc_73 (use{it_layout i32} (LocInfoE loc_74 ("n")))))))
        then
        locinfo: loc_55 ;
          Goto "#3"
        else
        locinfo: loc_42 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_55 ;
        if: LocInfoE loc_55 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_55 ((LocInfoE loc_56 (use{it_layout i32} (LocInfoE loc_58 ((LocInfoE loc_59 (!{LPtr} (LocInfoE loc_60 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_61 (use{it_layout i32} (LocInfoE loc_62 ("i")))))))) <{IntOp i32, IntOp i32} (LocInfoE loc_63 (use{it_layout i32} (LocInfoE loc_65 ((LocInfoE loc_66 (!{LPtr} (LocInfoE loc_67 ("ar")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_68 (use{it_layout i32} (LocInfoE loc_69 ("res")))))))))))
        then
        locinfo: loc_50 ;
          Goto "#6"
        else
        locinfo: loc_47 ;
          Goto "#7"
      ]> $
      <[ "#4" :=
        locinfo: loc_42 ;
        Return (LocInfoE loc_43 (use{it_layout i32} (LocInfoE loc_44 ("res"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_47 ;
        Goto "continue4"
      ]> $
      <[ "#6" :=
        locinfo: loc_50 ;
        LocInfoE loc_51 ("res") <-{ it_layout i32 }
          LocInfoE loc_52 (use{it_layout i32} (LocInfoE loc_53 ("i"))) ;
        locinfo: loc_47 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        locinfo: loc_47 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_81 ;
        Return (LocInfoE loc_82 (UnOp NegOp (IntOp i32) (LocInfoE loc_83 (i2v 1 i32))))
      ]> $
      <[ "#9" :=
        Goto "#1"
      ]> $
      <[ "continue4" :=
        LocInfoE loc_49 ("i") <-{ it_layout i32 }
          (use{it_layout i32} (LocInfoE loc_49 ("i"))) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
        locinfo: loc_41 ;
        Goto "#2"
      ]> $∅
    )%E
  |}.
End code.
