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
  Definition loc_80 : location_info := LocationInfo file_0 51 2 51 44.
  Definition loc_81 : location_info := LocationInfo file_0 52 2 52 13.
  Definition loc_82 : location_info := LocationInfo file_0 53 2 53 11.
  Definition loc_83 : location_info := LocationInfo file_0 53 9 53 10.
  Definition loc_84 : location_info := LocationInfo file_0 53 9 53 10.
  Definition loc_85 : location_info := LocationInfo file_0 52 10 52 12.
  Definition loc_86 : location_info := LocationInfo file_0 52 10 52 12.
  Definition loc_87 : location_info := LocationInfo file_0 52 11 52 12.
  Definition loc_88 : location_info := LocationInfo file_0 52 11 52 12.
  Definition loc_91 : location_info := LocationInfo file_0 51 2 51 3.
  Definition loc_92 : location_info := LocationInfo file_0 51 6 51 43.
  Definition loc_93 : location_info := LocationInfo file_0 51 32 51 35.
  Definition loc_94 : location_info := LocationInfo file_0 51 32 51 35.
  Definition loc_95 : location_info := LocationInfo file_0 51 39 51 42.
  Definition loc_96 : location_info := LocationInfo file_0 51 39 51 42.
  Definition loc_97 : location_info := LocationInfo file_0 50 11 50 19.
  Definition loc_98 : location_info := LocationInfo file_0 50 18 50 19.
  Definition loc_99 : location_info := LocationInfo file_0 50 18 50 19.
  Definition loc_102 : location_info := LocationInfo file_0 49 13 49 23.
  Definition loc_103 : location_info := LocationInfo file_0 49 22 49 23.
  Definition loc_104 : location_info := LocationInfo file_0 49 22 49 23.
  Definition loc_109 : location_info := LocationInfo file_0 61 2 61 30.
  Definition loc_110 : location_info := LocationInfo file_0 62 2 62 56.
  Definition loc_111 : location_info := LocationInfo file_0 63 2 63 12.
  Definition loc_112 : location_info := LocationInfo file_0 63 9 63 11.
  Definition loc_113 : location_info := LocationInfo file_0 63 9 63 11.
  Definition loc_114 : location_info := LocationInfo file_0 63 10 63 11.
  Definition loc_115 : location_info := LocationInfo file_0 63 10 63 11.
  Definition loc_116 : location_info := LocationInfo file_0 62 11 62 55.
  Definition loc_117 : location_info := LocationInfo file_0 62 37 62 40.
  Definition loc_118 : location_info := LocationInfo file_0 62 37 62 40.
  Definition loc_119 : location_info := LocationInfo file_0 62 44 62 54.
  Definition loc_120 : location_info := LocationInfo file_0 62 52 62 53.
  Definition loc_121 : location_info := LocationInfo file_0 62 52 62 53.
  Definition loc_124 : location_info := LocationInfo file_0 61 16 61 29.
  Definition loc_125 : location_info := LocationInfo file_0 61 28 61 29.
  Definition loc_126 : location_info := LocationInfo file_0 61 28 61 29.
  Definition loc_131 : location_info := LocationInfo file_0 71 2 71 24.
  Definition loc_132 : location_info := LocationInfo file_0 72 2 72 20.
  Definition loc_133 : location_info := LocationInfo file_0 73 2 73 50.
  Definition loc_134 : location_info := LocationInfo file_0 73 9 73 49.
  Definition loc_135 : location_info := LocationInfo file_0 73 9 73 49.
  Definition loc_136 : location_info := LocationInfo file_0 73 10 73 49.
  Definition loc_137 : location_info := LocationInfo file_0 73 37 73 40.
  Definition loc_138 : location_info := LocationInfo file_0 73 37 73 40.
  Definition loc_139 : location_info := LocationInfo file_0 73 44 73 47.
  Definition loc_140 : location_info := LocationInfo file_0 73 44 73 47.
  Definition loc_141 : location_info := LocationInfo file_0 72 11 72 19.
  Definition loc_142 : location_info := LocationInfo file_0 72 18 72 19.
  Definition loc_143 : location_info := LocationInfo file_0 72 18 72 19.
  Definition loc_146 : location_info := LocationInfo file_0 71 13 71 23.
  Definition loc_147 : location_info := LocationInfo file_0 71 22 71 23.
  Definition loc_148 : location_info := LocationInfo file_0 71 22 71 23.

  (* Definition of function [int_ptr]. *)
  Definition impl_int_ptr : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_6 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("p"))))) ;
        locinfo: loc_3 ;
        Return (LocInfoE loc_4 (use{it_layout size_t} (LocInfoE loc_5 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_ptr_val]. *)
  Definition impl_min_ptr_val : function := {|
    f_args := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
      ("i2", it_layout size_t);
      ("i1", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i1" <-{ it_layout size_t }
          LocInfoE loc_34 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_35 (use{void*} (LocInfoE loc_36 ("p1"))))) ;
        "i2" <-{ it_layout size_t }
          LocInfoE loc_29 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_30 (use{void*} (LocInfoE loc_31 ("p2"))))) ;
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
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_51 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_52 (use{void*} (LocInfoE loc_53 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_46 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ("i"))))) ;
        locinfo: loc_43 ;
        Return (LocInfoE loc_44 (use{void*} (LocInfoE loc_45 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip2]. *)
  Definition impl_roundtrip2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_71 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_72 (use{void*} (LocInfoE loc_73 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_66 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_66 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_67 (use{it_layout size_t} (LocInfoE loc_68 ("i"))))))) ;
        locinfo: loc_60 ;
        Return (LocInfoE loc_61 (CopyAllocId (LocInfoE loc_64 (use{void*} (LocInfoE loc_65 ("q")))) (LocInfoE loc_62 (use{void*} (LocInfoE loc_63 ("p"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read]. *)
  Definition impl_roundtrip_and_read : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("r", it_layout i32);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_102 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_103 (use{void*} (LocInfoE loc_104 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_97 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_98 (use{it_layout size_t} (LocInfoE loc_99 ("i"))))) ;
        locinfo: loc_80 ;
        LocInfoE loc_91 ("q") <-{ void* }
          LocInfoE loc_92 (CopyAllocId (LocInfoE loc_95 (use{void*} (LocInfoE loc_96 ("q")))) (LocInfoE loc_93 (use{void*} (LocInfoE loc_94 ("p"))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_85 (use{it_layout i32} (LocInfoE loc_87 (!{void*} (LocInfoE loc_88 ("q"))))) ;
        locinfo: loc_82 ;
        Return (LocInfoE loc_83 (use{it_layout i32} (LocInfoE loc_84 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read2]. *)
  Definition impl_roundtrip_and_read2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_124 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_125 (use{void*} (LocInfoE loc_126 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_116 (CopyAllocId (LocInfoE loc_119 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_120 (use{it_layout size_t} (LocInfoE loc_121 ("i")))))) (LocInfoE loc_117 (use{void*} (LocInfoE loc_118 ("p"))))) ;
        locinfo: loc_111 ;
        Return (LocInfoE loc_112 (use{it_layout i32} (LocInfoE loc_114 (!{void*} (LocInfoE loc_115 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read3]. *)
  Definition impl_roundtrip_and_read3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout size_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout size_t }
          LocInfoE loc_146 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_147 (use{void*} (LocInfoE loc_148 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_141 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_142 (use{it_layout size_t} (LocInfoE loc_143 ("i"))))) ;
        locinfo: loc_133 ;
        Return (LocInfoE loc_134 (use{it_layout i32} (LocInfoE loc_136 (LValue (LocInfoE loc_136 (CopyAllocId (LocInfoE loc_139 (use{void*} (LocInfoE loc_140 ("q")))) (LocInfoE loc_137 (use{void*} (LocInfoE loc_138 ("p"))))))))))
      ]> $∅
    )%E
  |}.
End code.
