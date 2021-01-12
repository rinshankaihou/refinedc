From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section code.
  Definition file_0 : string := "examples/intptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 8 2 8 24.
  Definition loc_3 : location_info := LocationInfo file_0 9 2 9 11.
  Definition loc_4 : location_info := LocationInfo file_0 9 9 9 10.
  Definition loc_5 : location_info := LocationInfo file_0 9 9 9 10.
  Definition loc_6 : location_info := LocationInfo file_0 8 13 8 23.
  Definition loc_7 : location_info := LocationInfo file_0 8 22 8 23.
  Definition loc_8 : location_info := LocationInfo file_0 8 22 8 23.
  Definition loc_13 : location_info := LocationInfo file_0 16 2 16 26.
  Definition loc_14 : location_info := LocationInfo file_0 17 2 17 26.
  Definition loc_15 : location_info := LocationInfo file_0 19 2 21 3.
  Definition loc_16 : location_info := LocationInfo file_0 23 2 23 12.
  Definition loc_17 : location_info := LocationInfo file_0 23 9 23 11.
  Definition loc_18 : location_info := LocationInfo file_0 23 9 23 11.
  Definition loc_19 : location_info := LocationInfo file_0 19 14 21 3.
  Definition loc_20 : location_info := LocationInfo file_0 20 4 20 14.
  Definition loc_21 : location_info := LocationInfo file_0 20 11 20 13.
  Definition loc_22 : location_info := LocationInfo file_0 20 11 20 13.
  Definition loc_24 : location_info := LocationInfo file_0 19 5 19 13.
  Definition loc_25 : location_info := LocationInfo file_0 19 5 19 7.
  Definition loc_26 : location_info := LocationInfo file_0 19 5 19 7.
  Definition loc_27 : location_info := LocationInfo file_0 19 11 19 13.
  Definition loc_28 : location_info := LocationInfo file_0 19 11 19 13.
  Definition loc_29 : location_info := LocationInfo file_0 17 14 17 25.
  Definition loc_30 : location_info := LocationInfo file_0 17 23 17 25.
  Definition loc_31 : location_info := LocationInfo file_0 17 23 17 25.
  Definition loc_34 : location_info := LocationInfo file_0 16 14 16 25.
  Definition loc_35 : location_info := LocationInfo file_0 16 23 16 25.
  Definition loc_36 : location_info := LocationInfo file_0 16 23 16 25.
  Definition loc_41 : location_info := LocationInfo file_0 30 2 30 24.
  Definition loc_42 : location_info := LocationInfo file_0 31 2 31 22.
  Definition loc_43 : location_info := LocationInfo file_0 32 2 32 11.
  Definition loc_44 : location_info := LocationInfo file_0 32 9 32 10.
  Definition loc_45 : location_info := LocationInfo file_0 32 9 32 10.
  Definition loc_46 : location_info := LocationInfo file_0 31 12 31 21.
  Definition loc_47 : location_info := LocationInfo file_0 31 20 31 21.
  Definition loc_48 : location_info := LocationInfo file_0 31 20 31 21.
  Definition loc_51 : location_info := LocationInfo file_0 30 13 30 23.
  Definition loc_52 : location_info := LocationInfo file_0 30 22 30 23.
  Definition loc_53 : location_info := LocationInfo file_0 30 22 30 23.
  Definition loc_58 : location_info := LocationInfo file_0 39 2 39 24.
  Definition loc_59 : location_info := LocationInfo file_0 40 2 40 21.
  Definition loc_60 : location_info := LocationInfo file_0 41 2 41 47.
  Definition loc_61 : location_info := LocationInfo file_0 41 9 41 46.
  Definition loc_62 : location_info := LocationInfo file_0 41 35 41 38.
  Definition loc_63 : location_info := LocationInfo file_0 41 35 41 38.
  Definition loc_64 : location_info := LocationInfo file_0 41 42 41 45.
  Definition loc_65 : location_info := LocationInfo file_0 41 42 41 45.
  Definition loc_66 : location_info := LocationInfo file_0 40 11 40 20.
  Definition loc_67 : location_info := LocationInfo file_0 40 19 40 20.
  Definition loc_68 : location_info := LocationInfo file_0 40 19 40 20.
  Definition loc_71 : location_info := LocationInfo file_0 39 13 39 23.
  Definition loc_72 : location_info := LocationInfo file_0 39 22 39 23.
  Definition loc_73 : location_info := LocationInfo file_0 39 22 39 23.
  Definition loc_78 : location_info := LocationInfo file_0 49 2 49 24.
  Definition loc_79 : location_info := LocationInfo file_0 50 2 50 20.
  Definition loc_80 : location_info := LocationInfo file_0 51 2 51 49.
  Definition loc_81 : location_info := LocationInfo file_0 52 2 52 12.
  Definition loc_82 : location_info := LocationInfo file_0 52 9 52 11.
  Definition loc_83 : location_info := LocationInfo file_0 52 9 52 11.
  Definition loc_84 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_85 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_86 : location_info := LocationInfo file_0 51 11 51 48.
  Definition loc_87 : location_info := LocationInfo file_0 51 37 51 40.
  Definition loc_88 : location_info := LocationInfo file_0 51 37 51 40.
  Definition loc_89 : location_info := LocationInfo file_0 51 44 51 47.
  Definition loc_90 : location_info := LocationInfo file_0 51 44 51 47.
  Definition loc_93 : location_info := LocationInfo file_0 50 11 50 19.
  Definition loc_94 : location_info := LocationInfo file_0 50 18 50 19.
  Definition loc_95 : location_info := LocationInfo file_0 50 18 50 19.
  Definition loc_98 : location_info := LocationInfo file_0 49 13 49 23.
  Definition loc_99 : location_info := LocationInfo file_0 49 22 49 23.
  Definition loc_100 : location_info := LocationInfo file_0 49 22 49 23.
  Definition loc_105 : location_info := LocationInfo file_0 60 2 60 30.
  Definition loc_106 : location_info := LocationInfo file_0 61 2 61 56.
  Definition loc_107 : location_info := LocationInfo file_0 62 2 62 12.
  Definition loc_108 : location_info := LocationInfo file_0 62 9 62 11.
  Definition loc_109 : location_info := LocationInfo file_0 62 9 62 11.
  Definition loc_110 : location_info := LocationInfo file_0 62 10 62 11.
  Definition loc_111 : location_info := LocationInfo file_0 62 10 62 11.
  Definition loc_112 : location_info := LocationInfo file_0 61 11 61 55.
  Definition loc_113 : location_info := LocationInfo file_0 61 37 61 40.
  Definition loc_114 : location_info := LocationInfo file_0 61 37 61 40.
  Definition loc_115 : location_info := LocationInfo file_0 61 44 61 54.
  Definition loc_116 : location_info := LocationInfo file_0 61 52 61 53.
  Definition loc_117 : location_info := LocationInfo file_0 61 52 61 53.
  Definition loc_120 : location_info := LocationInfo file_0 60 16 60 29.
  Definition loc_121 : location_info := LocationInfo file_0 60 28 60 29.
  Definition loc_122 : location_info := LocationInfo file_0 60 28 60 29.
  Definition loc_127 : location_info := LocationInfo file_0 71 2 71 24.
  Definition loc_128 : location_info := LocationInfo file_0 72 2 72 20.
  Definition loc_129 : location_info := LocationInfo file_0 73 2 73 50.
  Definition loc_130 : location_info := LocationInfo file_0 73 9 73 49.
  Definition loc_131 : location_info := LocationInfo file_0 73 9 73 49.
  Definition loc_132 : location_info := LocationInfo file_0 73 10 73 49.
  Definition loc_133 : location_info := LocationInfo file_0 73 37 73 40.
  Definition loc_134 : location_info := LocationInfo file_0 73 37 73 40.
  Definition loc_135 : location_info := LocationInfo file_0 73 44 73 47.
  Definition loc_136 : location_info := LocationInfo file_0 73 44 73 47.
  Definition loc_137 : location_info := LocationInfo file_0 72 11 72 19.
  Definition loc_138 : location_info := LocationInfo file_0 72 18 72 19.
  Definition loc_139 : location_info := LocationInfo file_0 72 18 72 19.
  Definition loc_142 : location_info := LocationInfo file_0 71 13 71 23.
  Definition loc_143 : location_info := LocationInfo file_0 71 22 71 23.
  Definition loc_144 : location_info := LocationInfo file_0 71 22 71 23.

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

  (* Definition of function [roundtrip_and_read2]. *)
  Definition impl_roundtrip_and_read2 : function := {|
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
          LocInfoE loc_120 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_121 (use{LPtr} (LocInfoE loc_122 ("p"))))) ;
        "q" <-{ LPtr }
          LocInfoE loc_112 (CopyAllocId (LocInfoE loc_115 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_116 (use{it_layout size_t} (LocInfoE loc_117 ("i")))))) (LocInfoE loc_113 (use{LPtr} (LocInfoE loc_114 ("p"))))) ;
        locinfo: loc_107 ;
        Return (LocInfoE loc_108 (use{it_layout i32} (LocInfoE loc_110 (!{LPtr} (LocInfoE loc_111 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read3]. *)
  Definition impl_roundtrip_and_read3 : function := {|
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
          LocInfoE loc_142 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_143 (use{LPtr} (LocInfoE loc_144 ("p"))))) ;
        "q" <-{ LPtr }
          LocInfoE loc_137 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_138 (use{it_layout size_t} (LocInfoE loc_139 ("i"))))) ;
        locinfo: loc_129 ;
        Return (LocInfoE loc_130 (use{it_layout i32} (LocInfoE loc_132 (CopyAllocId (LocInfoE loc_135 (!{LPtr} (LocInfoE loc_136 ("q")))) (LocInfoE loc_133 (!{LPtr} (LocInfoE loc_134 ("p"))))))))
      ]> $∅
    )%E
  |}.
End code.
