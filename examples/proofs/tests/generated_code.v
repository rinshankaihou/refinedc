From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section code.
  Definition file_0 : string := "examples/tests.c".
  Definition loc_2 : location_info := LocationInfo file_0 5 2 5 19.
  Definition loc_3 : location_info := LocationInfo file_0 6 2 6 13.
  Definition loc_4 : location_info := LocationInfo file_0 7 2 7 12.
  Definition loc_5 : location_info := LocationInfo file_0 8 2 8 14.
  Definition loc_6 : location_info := LocationInfo file_0 9 2 9 13.
  Definition loc_7 : location_info := LocationInfo file_0 11 2 11 21.
  Definition loc_8 : location_info := LocationInfo file_0 12 2 12 21.
  Definition loc_9 : location_info := LocationInfo file_0 13 2 13 21.
  Definition loc_10 : location_info := LocationInfo file_0 14 2 14 21.
  Definition loc_11 : location_info := LocationInfo file_0 15 2 15 21.
  Definition loc_12 : location_info := LocationInfo file_0 17 2 17 17.
  Definition loc_13 : location_info := LocationInfo file_0 18 2 18 16.
  Definition loc_14 : location_info := LocationInfo file_0 19 2 19 16.
  Definition loc_15 : location_info := LocationInfo file_0 20 2 20 16.
  Definition loc_16 : location_info := LocationInfo file_0 21 2 21 16.
  Definition loc_17 : location_info := LocationInfo file_0 23 2 23 9.
  Definition loc_19 : location_info := LocationInfo file_0 21 9 21 16.
  Definition loc_22 : location_info := LocationInfo file_0 21 5 21 7.
  Definition loc_24 : location_info := LocationInfo file_0 21 6 21 7.
  Definition loc_25 : location_info := LocationInfo file_0 21 6 21 7.
  Definition loc_26 : location_info := LocationInfo file_0 20 9 20 16.
  Definition loc_29 : location_info := LocationInfo file_0 20 5 20 7.
  Definition loc_31 : location_info := LocationInfo file_0 20 6 20 7.
  Definition loc_32 : location_info := LocationInfo file_0 20 6 20 7.
  Definition loc_33 : location_info := LocationInfo file_0 19 9 19 16.
  Definition loc_36 : location_info := LocationInfo file_0 19 5 19 7.
  Definition loc_38 : location_info := LocationInfo file_0 19 6 19 7.
  Definition loc_39 : location_info := LocationInfo file_0 19 6 19 7.
  Definition loc_40 : location_info := LocationInfo file_0 18 9 18 16.
  Definition loc_43 : location_info := LocationInfo file_0 18 5 18 7.
  Definition loc_45 : location_info := LocationInfo file_0 18 6 18 7.
  Definition loc_46 : location_info := LocationInfo file_0 18 6 18 7.
  Definition loc_47 : location_info := LocationInfo file_0 17 10 17 17.
  Definition loc_50 : location_info := LocationInfo file_0 17 5 17 8.
  Definition loc_52 : location_info := LocationInfo file_0 17 6 17 8.
  Definition loc_53 : location_info := LocationInfo file_0 17 6 17 8.
  Definition loc_54 : location_info := LocationInfo file_0 15 14 15 21.
  Definition loc_57 : location_info := LocationInfo file_0 15 5 15 12.
  Definition loc_58 : location_info := LocationInfo file_0 15 5 15 7.
  Definition loc_59 : location_info := LocationInfo file_0 15 5 15 7.
  Definition loc_60 : location_info := LocationInfo file_0 15 11 15 12.
  Definition loc_61 : location_info := LocationInfo file_0 15 11 15 12.
  Definition loc_62 : location_info := LocationInfo file_0 14 14 14 21.
  Definition loc_65 : location_info := LocationInfo file_0 14 5 14 12.
  Definition loc_66 : location_info := LocationInfo file_0 14 5 14 7.
  Definition loc_67 : location_info := LocationInfo file_0 14 5 14 7.
  Definition loc_68 : location_info := LocationInfo file_0 14 11 14 12.
  Definition loc_69 : location_info := LocationInfo file_0 14 11 14 12.
  Definition loc_70 : location_info := LocationInfo file_0 13 14 13 21.
  Definition loc_73 : location_info := LocationInfo file_0 13 5 13 12.
  Definition loc_74 : location_info := LocationInfo file_0 13 5 13 7.
  Definition loc_75 : location_info := LocationInfo file_0 13 5 13 7.
  Definition loc_76 : location_info := LocationInfo file_0 13 11 13 12.
  Definition loc_77 : location_info := LocationInfo file_0 13 11 13 12.
  Definition loc_78 : location_info := LocationInfo file_0 12 14 12 21.
  Definition loc_81 : location_info := LocationInfo file_0 12 5 12 12.
  Definition loc_82 : location_info := LocationInfo file_0 12 5 12 7.
  Definition loc_83 : location_info := LocationInfo file_0 12 5 12 7.
  Definition loc_84 : location_info := LocationInfo file_0 12 11 12 12.
  Definition loc_85 : location_info := LocationInfo file_0 12 11 12 12.
  Definition loc_86 : location_info := LocationInfo file_0 11 14 11 21.
  Definition loc_89 : location_info := LocationInfo file_0 11 5 11 12.
  Definition loc_90 : location_info := LocationInfo file_0 11 5 11 7.
  Definition loc_91 : location_info := LocationInfo file_0 11 5 11 7.
  Definition loc_92 : location_info := LocationInfo file_0 11 11 11 12.
  Definition loc_93 : location_info := LocationInfo file_0 11 11 11 12.
  Definition loc_94 : location_info := LocationInfo file_0 9 11 9 12.
  Definition loc_97 : location_info := LocationInfo file_0 8 12 8 13.
  Definition loc_100 : location_info := LocationInfo file_0 7 10 7 11.
  Definition loc_103 : location_info := LocationInfo file_0 6 11 6 12.
  Definition loc_106 : location_info := LocationInfo file_0 5 17 5 18.

  (* Definition of function [test1]. *)
  Definition impl_test1 : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("c", it_layout u8);
      ("s", it_layout i16);
      ("ll", it_layout i64);
      ("l", it_layout i64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ll" <-{ it_layout i64 }
          LocInfoE loc_106 (UnOp (CastOp $ IntOp i64) (IntOp i32) (LocInfoE loc_106 (i2v 0 i32))) ;
        "l" <-{ it_layout i64 }
          LocInfoE loc_103 (UnOp (CastOp $ IntOp i64) (IntOp i32) (LocInfoE loc_103 (i2v 0 i32))) ;
        "i" <-{ it_layout i32 } LocInfoE loc_100 (i2v 0 i32) ;
        "s" <-{ it_layout i16 }
          LocInfoE loc_97 (UnOp (CastOp $ IntOp i16) (IntOp i32) (LocInfoE loc_97 (i2v 0 i32))) ;
        "c" <-{ it_layout u8 }
          LocInfoE loc_94 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_94 (i2v 0 i32))) ;
        locinfo: loc_89 ;
        if: LocInfoE loc_89 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_89 ((LocInfoE loc_90 (use{it_layout i64} (LocInfoE loc_91 ("ll")))) ={IntOp i64, IntOp i64} (LocInfoE loc_92 (use{it_layout i64} (LocInfoE loc_93 ("l")))))))
        then
        locinfo: loc_86 ;
          Goto "#29"
        else
        locinfo: loc_81 ;
          Goto "#30"
      ]> $
      <[ "#1" :=
        locinfo: loc_81 ;
        if: LocInfoE loc_81 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_81 ((LocInfoE loc_82 (use{it_layout i64} (LocInfoE loc_83 ("ll")))) ={IntOp i64, IntOp i64} (LocInfoE loc_84 (use{it_layout i64} (LocInfoE loc_85 ("l")))))))
        then
        locinfo: loc_78 ;
          Goto "#27"
        else
        locinfo: loc_73 ;
          Goto "#28"
      ]> $
      <[ "#10" :=
        locinfo: loc_17 ;
        Return (VOID)
      ]> $
      <[ "#11" :=
        locinfo: loc_19 ;
        Return (VOID)
      ]> $
      <[ "#12" :=
        locinfo: loc_17 ;
        Goto "#10"
      ]> $
      <[ "#13" :=
        locinfo: loc_26 ;
        Return (VOID)
      ]> $
      <[ "#14" :=
        locinfo: loc_22 ;
        Goto "#9"
      ]> $
      <[ "#15" :=
        locinfo: loc_33 ;
        Return (VOID)
      ]> $
      <[ "#16" :=
        locinfo: loc_29 ;
        Goto "#8"
      ]> $
      <[ "#17" :=
        locinfo: loc_40 ;
        Return (VOID)
      ]> $
      <[ "#18" :=
        locinfo: loc_36 ;
        Goto "#7"
      ]> $
      <[ "#19" :=
        locinfo: loc_47 ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_73 ;
        if: LocInfoE loc_73 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_73 ((LocInfoE loc_74 (use{it_layout i64} (LocInfoE loc_75 ("ll")))) ={IntOp i64, IntOp i64} (LocInfoE loc_76 (use{it_layout i32} (LocInfoE loc_77 ("i")))))))
        then
        locinfo: loc_70 ;
          Goto "#25"
        else
        locinfo: loc_65 ;
          Goto "#26"
      ]> $
      <[ "#20" :=
        locinfo: loc_43 ;
        Goto "#6"
      ]> $
      <[ "#21" :=
        locinfo: loc_54 ;
        Return (VOID)
      ]> $
      <[ "#22" :=
        locinfo: loc_50 ;
        Goto "#5"
      ]> $
      <[ "#23" :=
        locinfo: loc_62 ;
        Return (VOID)
      ]> $
      <[ "#24" :=
        locinfo: loc_57 ;
        Goto "#4"
      ]> $
      <[ "#25" :=
        locinfo: loc_70 ;
        Return (VOID)
      ]> $
      <[ "#26" :=
        locinfo: loc_65 ;
        Goto "#3"
      ]> $
      <[ "#27" :=
        locinfo: loc_78 ;
        Return (VOID)
      ]> $
      <[ "#28" :=
        locinfo: loc_73 ;
        Goto "#2"
      ]> $
      <[ "#29" :=
        locinfo: loc_86 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        locinfo: loc_65 ;
        if: LocInfoE loc_65 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_65 ((LocInfoE loc_66 (use{it_layout i64} (LocInfoE loc_67 ("ll")))) ={IntOp i64, IntOp i64} (LocInfoE loc_68 (use{it_layout i16} (LocInfoE loc_69 ("s")))))))
        then
        locinfo: loc_62 ;
          Goto "#23"
        else
        locinfo: loc_57 ;
          Goto "#24"
      ]> $
      <[ "#30" :=
        locinfo: loc_81 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_57 ;
        if: LocInfoE loc_57 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_57 ((LocInfoE loc_58 (use{it_layout i64} (LocInfoE loc_59 ("ll")))) ={IntOp i64, IntOp i64} (LocInfoE loc_60 (use{it_layout u8} (LocInfoE loc_61 ("c")))))))
        then
        locinfo: loc_54 ;
          Goto "#21"
        else
        locinfo: loc_50 ;
          Goto "#22"
      ]> $
      <[ "#5" :=
        locinfo: loc_50 ;
        if: LocInfoE loc_50 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_50 ((i2v 0 i32) ={IntOp i64, IntOp i64} (LocInfoE loc_52 (use{it_layout i64} (LocInfoE loc_53 ("ll")))))))
        then
        locinfo: loc_47 ;
          Goto "#19"
        else
        locinfo: loc_43 ;
          Goto "#20"
      ]> $
      <[ "#6" :=
        locinfo: loc_43 ;
        if: LocInfoE loc_43 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_43 ((i2v 0 i32) ={IntOp i64, IntOp i64} (LocInfoE loc_45 (use{it_layout i64} (LocInfoE loc_46 ("l")))))))
        then
        locinfo: loc_40 ;
          Goto "#17"
        else
        locinfo: loc_36 ;
          Goto "#18"
      ]> $
      <[ "#7" :=
        locinfo: loc_36 ;
        if: LocInfoE loc_36 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_36 ((i2v 0 i32) ={IntOp i32, IntOp i32} (LocInfoE loc_38 (use{it_layout i32} (LocInfoE loc_39 ("i")))))))
        then
        locinfo: loc_33 ;
          Goto "#15"
        else
        locinfo: loc_29 ;
          Goto "#16"
      ]> $
      <[ "#8" :=
        locinfo: loc_29 ;
        if: LocInfoE loc_29 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_29 ((i2v 0 i32) ={IntOp i32, IntOp i32} (LocInfoE loc_31 (use{it_layout i16} (LocInfoE loc_32 ("s")))))))
        then
        locinfo: loc_26 ;
          Goto "#13"
        else
        locinfo: loc_22 ;
          Goto "#14"
      ]> $
      <[ "#9" :=
        locinfo: loc_22 ;
        if: LocInfoE loc_22 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_22 ((i2v 0 i32) ={IntOp i32, IntOp i32} (LocInfoE loc_24 (use{it_layout u8} (LocInfoE loc_25 ("c")))))))
        then
        locinfo: loc_19 ;
          Goto "#11"
        else
        locinfo: loc_17 ;
          Goto "#12"
      ]> $∅
    )%E
  |}.
End code.
