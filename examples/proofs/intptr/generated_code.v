From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section code.
  Definition file_0 : string := "examples/intptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 7 2 7 24.
  Definition loc_3 : location_info := LocationInfo file_0 8 2 8 11.
  Definition loc_4 : location_info := LocationInfo file_0 8 9 8 10.
  Definition loc_5 : location_info := LocationInfo file_0 8 9 8 10.
  Definition loc_6 : location_info := LocationInfo file_0 7 13 7 23.
  Definition loc_7 : location_info := LocationInfo file_0 7 22 7 23.
  Definition loc_8 : location_info := LocationInfo file_0 7 22 7 23.
  Definition loc_13 : location_info := LocationInfo file_0 15 2 15 26.
  Definition loc_14 : location_info := LocationInfo file_0 16 2 16 26.
  Definition loc_15 : location_info := LocationInfo file_0 18 2 20 3.
  Definition loc_16 : location_info := LocationInfo file_0 22 2 22 12.
  Definition loc_17 : location_info := LocationInfo file_0 22 9 22 11.
  Definition loc_18 : location_info := LocationInfo file_0 22 9 22 11.
  Definition loc_19 : location_info := LocationInfo file_0 18 14 20 3.
  Definition loc_20 : location_info := LocationInfo file_0 19 4 19 14.
  Definition loc_21 : location_info := LocationInfo file_0 19 11 19 13.
  Definition loc_22 : location_info := LocationInfo file_0 19 11 19 13.
  Definition loc_24 : location_info := LocationInfo file_0 18 5 18 13.
  Definition loc_25 : location_info := LocationInfo file_0 18 5 18 7.
  Definition loc_26 : location_info := LocationInfo file_0 18 5 18 7.
  Definition loc_27 : location_info := LocationInfo file_0 18 11 18 13.
  Definition loc_28 : location_info := LocationInfo file_0 18 11 18 13.
  Definition loc_29 : location_info := LocationInfo file_0 16 14 16 25.
  Definition loc_30 : location_info := LocationInfo file_0 16 23 16 25.
  Definition loc_31 : location_info := LocationInfo file_0 16 23 16 25.
  Definition loc_34 : location_info := LocationInfo file_0 15 14 15 25.
  Definition loc_35 : location_info := LocationInfo file_0 15 23 15 25.
  Definition loc_36 : location_info := LocationInfo file_0 15 23 15 25.
  Definition loc_41 : location_info := LocationInfo file_0 29 2 29 24.
  Definition loc_42 : location_info := LocationInfo file_0 30 2 30 22.
  Definition loc_43 : location_info := LocationInfo file_0 31 2 31 11.
  Definition loc_44 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_45 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_46 : location_info := LocationInfo file_0 30 12 30 21.
  Definition loc_47 : location_info := LocationInfo file_0 30 20 30 21.
  Definition loc_48 : location_info := LocationInfo file_0 30 20 30 21.
  Definition loc_51 : location_info := LocationInfo file_0 29 13 29 23.
  Definition loc_52 : location_info := LocationInfo file_0 29 22 29 23.
  Definition loc_53 : location_info := LocationInfo file_0 29 22 29 23.
  Definition loc_58 : location_info := LocationInfo file_0 38 2 38 24.
  Definition loc_59 : location_info := LocationInfo file_0 39 2 39 21.
  Definition loc_60 : location_info := LocationInfo file_0 40 2 40 47.
  Definition loc_61 : location_info := LocationInfo file_0 40 9 40 46.
  Definition loc_62 : location_info := LocationInfo file_0 40 35 40 38.
  Definition loc_63 : location_info := LocationInfo file_0 40 35 40 38.
  Definition loc_64 : location_info := LocationInfo file_0 40 42 40 45.
  Definition loc_65 : location_info := LocationInfo file_0 40 42 40 45.
  Definition loc_66 : location_info := LocationInfo file_0 39 11 39 20.
  Definition loc_67 : location_info := LocationInfo file_0 39 19 39 20.
  Definition loc_68 : location_info := LocationInfo file_0 39 19 39 20.
  Definition loc_71 : location_info := LocationInfo file_0 38 13 38 23.
  Definition loc_72 : location_info := LocationInfo file_0 38 22 38 23.
  Definition loc_73 : location_info := LocationInfo file_0 38 22 38 23.
  Definition loc_78 : location_info := LocationInfo file_0 48 2 48 24.
  Definition loc_79 : location_info := LocationInfo file_0 49 2 49 20.
  Definition loc_80 : location_info := LocationInfo file_0 50 2 50 49.
  Definition loc_81 : location_info := LocationInfo file_0 51 2 51 12.
  Definition loc_82 : location_info := LocationInfo file_0 51 9 51 11.
  Definition loc_83 : location_info := LocationInfo file_0 51 9 51 11.
  Definition loc_84 : location_info := LocationInfo file_0 51 10 51 11.
  Definition loc_85 : location_info := LocationInfo file_0 51 10 51 11.
  Definition loc_86 : location_info := LocationInfo file_0 50 11 50 48.
  Definition loc_87 : location_info := LocationInfo file_0 50 37 50 40.
  Definition loc_88 : location_info := LocationInfo file_0 50 37 50 40.
  Definition loc_89 : location_info := LocationInfo file_0 50 44 50 47.
  Definition loc_90 : location_info := LocationInfo file_0 50 44 50 47.
  Definition loc_93 : location_info := LocationInfo file_0 49 11 49 19.
  Definition loc_94 : location_info := LocationInfo file_0 49 18 49 19.
  Definition loc_95 : location_info := LocationInfo file_0 49 18 49 19.
  Definition loc_98 : location_info := LocationInfo file_0 48 13 48 23.
  Definition loc_99 : location_info := LocationInfo file_0 48 22 48 23.
  Definition loc_100 : location_info := LocationInfo file_0 48 22 48 23.

  (* Definition of function [int_ptr]. *)
  Definition impl_int_ptr : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("i", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_6 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_7 (use{LPtr} (LocInfoE loc_8 ("p"))))) ;
        locinfo: loc_3 ;
        Return (LocInfoE loc_4 (use{it_layout size_t} (LocInfoE loc_5 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_ptr_val]. *)
  Definition impl_min_ptr_val : function := {|
    f_args := [
      ("p1", LPtr);
      ("p2", LPtr)
    ];
    f_local_vars := [
      ("i2", it_layout size_t);
      ("i1", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i1" <-{ it_layout size_t }
          LocInfoE loc_34 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_35 (use{LPtr} (LocInfoE loc_36 ("p1"))))) ;
        "i2" <-{ it_layout size_t }
          LocInfoE loc_29 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_30 (use{LPtr} (LocInfoE loc_31 ("p2"))))) ;
        locinfo: loc_24 ;
        if: LocInfoE loc_24 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_24 ((LocInfoE loc_25 (use{it_layout size_t} (LocInfoE loc_26 ("i1")))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_27 (use{it_layout size_t} (LocInfoE loc_28 ("i2")))))))
        then
        locinfo: loc_20 ;
          Goto "#2"
        else
        locinfo: loc_16 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_16 ;
        Return (LocInfoE loc_17 (use{it_layout size_t} (LocInfoE loc_18 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_20 ;
        Return (LocInfoE loc_21 (use{it_layout size_t} (LocInfoE loc_22 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_16 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip1]. *)
  Definition impl_roundtrip1 : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("q", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_51 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_52 (use{LPtr} (LocInfoE loc_53 ("p"))))) ;
        "q" <-{ LPtr }
          LocInfoE loc_46 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ("i"))))) ;
        locinfo: loc_43 ;
        Return (LocInfoE loc_44 (use{LPtr} (LocInfoE loc_45 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip2]. *)
  Definition impl_roundtrip2 : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("q", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_71 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_72 (use{LPtr} (LocInfoE loc_73 ("p"))))) ;
        "q" <-{ LPtr }
          LocInfoE loc_66 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_66 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_67 (use{it_layout size_t} (LocInfoE loc_68 ("i"))))))) ;
        locinfo: loc_60 ;
        Return (LocInfoE loc_61 (CopyAllocId (LocInfoE loc_64 (use{LPtr} (LocInfoE loc_65 ("q")))) (LocInfoE loc_62 (use{LPtr} (LocInfoE loc_63 ("p"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read]. *)
  Definition impl_roundtrip_and_read : function := {|
    f_args := [
      ("p", LPtr)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("r", LPtr);
      ("q", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_98 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_99 (use{LPtr} (LocInfoE loc_100 ("p"))))) ;
        "q" <-{ LPtr }
          LocInfoE loc_93 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_94 (use{it_layout size_t} (LocInfoE loc_95 ("i"))))) ;
        "r" <-{ LPtr }
          LocInfoE loc_86 (CopyAllocId (LocInfoE loc_89 (use{LPtr} (LocInfoE loc_90 ("q")))) (LocInfoE loc_87 (use{LPtr} (LocInfoE loc_88 ("p"))))) ;
        locinfo: loc_81 ;
        Return (LocInfoE loc_82 (use{it_layout i32} (LocInfoE loc_84 (!{LPtr} (LocInfoE loc_85 ("r"))))))
      ]> $∅
    )%E
  |}.
End code.
