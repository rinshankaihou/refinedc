From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section code.
  Definition file_0 : string := "examples/queue.c".
  Definition loc_2 : location_info := LocationInfo file_0 28 2 28 46.
  Definition loc_3 : location_info := LocationInfo file_0 29 2 29 31.
  Definition loc_4 : location_info := LocationInfo file_0 30 2 30 29.
  Definition loc_5 : location_info := LocationInfo file_0 31 2 31 15.
  Definition loc_6 : location_info := LocationInfo file_0 31 9 31 14.
  Definition loc_7 : location_info := LocationInfo file_0 31 9 31 14.
  Definition loc_8 : location_info := LocationInfo file_0 30 2 30 13.
  Definition loc_9 : location_info := LocationInfo file_0 30 2 30 7.
  Definition loc_10 : location_info := LocationInfo file_0 30 2 30 7.
  Definition loc_11 : location_info := LocationInfo file_0 30 16 30 28.
  Definition loc_12 : location_info := LocationInfo file_0 30 17 30 28.
  Definition loc_13 : location_info := LocationInfo file_0 30 17 30 22.
  Definition loc_14 : location_info := LocationInfo file_0 30 17 30 22.
  Definition loc_15 : location_info := LocationInfo file_0 29 2 29 13.
  Definition loc_16 : location_info := LocationInfo file_0 29 2 29 7.
  Definition loc_17 : location_info := LocationInfo file_0 29 2 29 7.
  Definition loc_18 : location_info := LocationInfo file_0 29 16 29 30.
  Definition loc_19 : location_info := LocationInfo file_0 28 18 28 45.
  Definition loc_20 : location_info := LocationInfo file_0 28 18 28 23.
  Definition loc_21 : location_info := LocationInfo file_0 28 18 28 23.
  Definition loc_22 : location_info := LocationInfo file_0 28 24 28 44.
  Definition loc_27 : location_info := LocationInfo file_0 39 2 39 17.
  Definition loc_28 : location_info := LocationInfo file_0 39 17 39 3.
  Definition loc_29 : location_info := LocationInfo file_0 40 2 40 38.
  Definition loc_30 : location_info := LocationInfo file_0 40 9 40 37.
  Definition loc_31 : location_info := LocationInfo file_0 40 9 40 19.
  Definition loc_32 : location_info := LocationInfo file_0 40 9 40 19.
  Definition loc_33 : location_info := LocationInfo file_0 40 9 40 13.
  Definition loc_34 : location_info := LocationInfo file_0 40 9 40 13.
  Definition loc_35 : location_info := LocationInfo file_0 40 11 40 12.
  Definition loc_36 : location_info := LocationInfo file_0 40 11 40 12.
  Definition loc_37 : location_info := LocationInfo file_0 40 23 40 37.
  Definition loc_38 : location_info := LocationInfo file_0 39 2 39 16.
  Definition loc_39 : location_info := LocationInfo file_0 39 3 39 16.
  Definition loc_40 : location_info := LocationInfo file_0 39 5 39 15.
  Definition loc_41 : location_info := LocationInfo file_0 39 5 39 15.
  Definition loc_42 : location_info := LocationInfo file_0 39 5 39 9.
  Definition loc_43 : location_info := LocationInfo file_0 39 5 39 9.
  Definition loc_44 : location_info := LocationInfo file_0 39 7 39 8.
  Definition loc_45 : location_info := LocationInfo file_0 39 7 39 8.
  Definition loc_48 : location_info := LocationInfo file_0 48 2 48 55.
  Definition loc_49 : location_info := LocationInfo file_0 49 2 49 17.
  Definition loc_50 : location_info := LocationInfo file_0 50 2 50 30.
  Definition loc_51 : location_info := LocationInfo file_0 51 2 51 21.
  Definition loc_52 : location_info := LocationInfo file_0 52 2 52 27.
  Definition loc_53 : location_info := LocationInfo file_0 52 2 52 12.
  Definition loc_54 : location_info := LocationInfo file_0 52 2 52 6.
  Definition loc_55 : location_info := LocationInfo file_0 52 2 52 6.
  Definition loc_56 : location_info := LocationInfo file_0 52 4 52 5.
  Definition loc_57 : location_info := LocationInfo file_0 52 4 52 5.
  Definition loc_58 : location_info := LocationInfo file_0 52 15 52 26.
  Definition loc_59 : location_info := LocationInfo file_0 52 16 52 26.
  Definition loc_60 : location_info := LocationInfo file_0 52 16 52 20.
  Definition loc_61 : location_info := LocationInfo file_0 52 16 52 20.
  Definition loc_62 : location_info := LocationInfo file_0 51 2 51 13.
  Definition loc_63 : location_info := LocationInfo file_0 51 3 51 13.
  Definition loc_64 : location_info := LocationInfo file_0 51 3 51 13.
  Definition loc_65 : location_info := LocationInfo file_0 51 3 51 7.
  Definition loc_66 : location_info := LocationInfo file_0 51 3 51 7.
  Definition loc_67 : location_info := LocationInfo file_0 51 5 51 6.
  Definition loc_68 : location_info := LocationInfo file_0 51 5 51 6.
  Definition loc_69 : location_info := LocationInfo file_0 51 16 51 20.
  Definition loc_70 : location_info := LocationInfo file_0 51 16 51 20.
  Definition loc_71 : location_info := LocationInfo file_0 50 2 50 12.
  Definition loc_72 : location_info := LocationInfo file_0 50 2 50 6.
  Definition loc_73 : location_info := LocationInfo file_0 50 2 50 6.
  Definition loc_74 : location_info := LocationInfo file_0 50 15 50 29.
  Definition loc_75 : location_info := LocationInfo file_0 49 2 49 12.
  Definition loc_76 : location_info := LocationInfo file_0 49 2 49 6.
  Definition loc_77 : location_info := LocationInfo file_0 49 2 49 6.
  Definition loc_78 : location_info := LocationInfo file_0 49 15 49 16.
  Definition loc_79 : location_info := LocationInfo file_0 49 15 49 16.
  Definition loc_80 : location_info := LocationInfo file_0 48 22 48 54.
  Definition loc_81 : location_info := LocationInfo file_0 48 22 48 27.
  Definition loc_82 : location_info := LocationInfo file_0 48 22 48 27.
  Definition loc_83 : location_info := LocationInfo file_0 48 28 48 53.
  Definition loc_88 : location_info := LocationInfo file_0 61 2 61 17.
  Definition loc_89 : location_info := LocationInfo file_0 61 17 61 3.
  Definition loc_90 : location_info := LocationInfo file_0 62 2 64 3.
  Definition loc_91 : location_info := LocationInfo file_0 65 2 65 33.
  Definition loc_92 : location_info := LocationInfo file_0 66 2 66 25.
  Definition loc_93 : location_info := LocationInfo file_0 67 2 72 3.
  Definition loc_94 : location_info := LocationInfo file_0 73 2 73 40.
  Definition loc_95 : location_info := LocationInfo file_0 74 2 74 13.
  Definition loc_96 : location_info := LocationInfo file_0 74 9 74 12.
  Definition loc_97 : location_info := LocationInfo file_0 74 9 74 12.
  Definition loc_98 : location_info := LocationInfo file_0 73 2 73 6.
  Definition loc_99 : location_info := LocationInfo file_0 73 2 73 6.
  Definition loc_100 : location_info := LocationInfo file_0 73 7 73 32.
  Definition loc_101 : location_info := LocationInfo file_0 73 34 73 38.
  Definition loc_102 : location_info := LocationInfo file_0 73 34 73 38.
  Definition loc_103 : location_info := LocationInfo file_0 67 35 70 3.
  Definition loc_104 : location_info := LocationInfo file_0 68 4 68 32.
  Definition loc_105 : location_info := LocationInfo file_0 69 4 69 29.
  Definition loc_106 : location_info := LocationInfo file_0 69 4 69 14.
  Definition loc_107 : location_info := LocationInfo file_0 69 4 69 8.
  Definition loc_108 : location_info := LocationInfo file_0 69 4 69 8.
  Definition loc_109 : location_info := LocationInfo file_0 69 6 69 7.
  Definition loc_110 : location_info := LocationInfo file_0 69 6 69 7.
  Definition loc_111 : location_info := LocationInfo file_0 69 17 69 28.
  Definition loc_112 : location_info := LocationInfo file_0 69 18 69 28.
  Definition loc_113 : location_info := LocationInfo file_0 69 18 69 22.
  Definition loc_114 : location_info := LocationInfo file_0 69 18 69 22.
  Definition loc_115 : location_info := LocationInfo file_0 69 20 69 21.
  Definition loc_116 : location_info := LocationInfo file_0 69 20 69 21.
  Definition loc_117 : location_info := LocationInfo file_0 68 4 68 14.
  Definition loc_118 : location_info := LocationInfo file_0 68 4 68 8.
  Definition loc_119 : location_info := LocationInfo file_0 68 4 68 8.
  Definition loc_120 : location_info := LocationInfo file_0 68 6 68 7.
  Definition loc_121 : location_info := LocationInfo file_0 68 6 68 7.
  Definition loc_122 : location_info := LocationInfo file_0 68 17 68 31.
  Definition loc_123 : location_info := LocationInfo file_0 70 9 72 3.
  Definition loc_124 : location_info := LocationInfo file_0 71 4 71 28.
  Definition loc_125 : location_info := LocationInfo file_0 71 4 71 14.
  Definition loc_126 : location_info := LocationInfo file_0 71 4 71 8.
  Definition loc_127 : location_info := LocationInfo file_0 71 4 71 8.
  Definition loc_128 : location_info := LocationInfo file_0 71 6 71 7.
  Definition loc_129 : location_info := LocationInfo file_0 71 6 71 7.
  Definition loc_130 : location_info := LocationInfo file_0 71 17 71 27.
  Definition loc_131 : location_info := LocationInfo file_0 71 17 71 27.
  Definition loc_132 : location_info := LocationInfo file_0 71 17 71 21.
  Definition loc_133 : location_info := LocationInfo file_0 71 17 71 21.
  Definition loc_134 : location_info := LocationInfo file_0 67 5 67 33.
  Definition loc_135 : location_info := LocationInfo file_0 67 5 67 15.
  Definition loc_136 : location_info := LocationInfo file_0 67 5 67 15.
  Definition loc_137 : location_info := LocationInfo file_0 67 5 67 9.
  Definition loc_138 : location_info := LocationInfo file_0 67 5 67 9.
  Definition loc_139 : location_info := LocationInfo file_0 67 19 67 33.
  Definition loc_140 : location_info := LocationInfo file_0 66 14 66 24.
  Definition loc_141 : location_info := LocationInfo file_0 66 14 66 24.
  Definition loc_142 : location_info := LocationInfo file_0 66 14 66 18.
  Definition loc_143 : location_info := LocationInfo file_0 66 14 66 18.
  Definition loc_146 : location_info := LocationInfo file_0 65 22 65 32.
  Definition loc_147 : location_info := LocationInfo file_0 65 22 65 32.
  Definition loc_148 : location_info := LocationInfo file_0 65 22 65 26.
  Definition loc_149 : location_info := LocationInfo file_0 65 22 65 26.
  Definition loc_150 : location_info := LocationInfo file_0 65 24 65 25.
  Definition loc_151 : location_info := LocationInfo file_0 65 24 65 25.
  Definition loc_154 : location_info := LocationInfo file_0 62 36 64 3.
  Definition loc_155 : location_info := LocationInfo file_0 63 4 63 26.
  Definition loc_156 : location_info := LocationInfo file_0 63 11 63 25.
  Definition loc_158 : location_info := LocationInfo file_0 62 6 62 34.
  Definition loc_159 : location_info := LocationInfo file_0 62 6 62 16.
  Definition loc_160 : location_info := LocationInfo file_0 62 6 62 16.
  Definition loc_161 : location_info := LocationInfo file_0 62 6 62 10.
  Definition loc_162 : location_info := LocationInfo file_0 62 6 62 10.
  Definition loc_163 : location_info := LocationInfo file_0 62 8 62 9.
  Definition loc_164 : location_info := LocationInfo file_0 62 8 62 9.
  Definition loc_165 : location_info := LocationInfo file_0 62 20 62 34.
  Definition loc_166 : location_info := LocationInfo file_0 61 2 61 16.
  Definition loc_167 : location_info := LocationInfo file_0 61 3 61 16.
  Definition loc_168 : location_info := LocationInfo file_0 61 5 61 15.
  Definition loc_169 : location_info := LocationInfo file_0 61 5 61 15.
  Definition loc_170 : location_info := LocationInfo file_0 61 5 61 9.
  Definition loc_171 : location_info := LocationInfo file_0 61 5 61 9.
  Definition loc_172 : location_info := LocationInfo file_0 61 7 61 8.
  Definition loc_173 : location_info := LocationInfo file_0 61 7 61 8.

  (* Definition of struct [queue_elem]. *)
  Program Definition struct_queue_elem := {|
    sl_members := [
      (Some "elem", LPtr);
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [queue]. *)
  Program Definition struct_queue := {|
    sl_members := [
      (Some "head", LPtr);
      (Some "tail", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [init_queue]. *)
  Definition impl_init_queue (alloc : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("queue", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_19 ;
        "$0" <- LocInfoE loc_21 (alloc) with
          [ LocInfoE loc_22 (i2v (layout_of struct_queue).(ly_size) size_t) ] ;
        "queue" <-{ LPtr }
          LocInfoE loc_19 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_19 ("$0"))) ;
        locinfo: loc_3 ;
        LocInfoE loc_15 ((LocInfoE loc_16 (!{LPtr} (LocInfoE loc_17 ("queue")))) at{struct_queue} "head") <-{ LPtr }
          LocInfoE loc_18 (NULL) ;
        locinfo: loc_4 ;
        LocInfoE loc_8 ((LocInfoE loc_9 (!{LPtr} (LocInfoE loc_10 ("queue")))) at{struct_queue} "tail") <-{ LPtr }
          LocInfoE loc_11 (&(LocInfoE loc_12 ((LocInfoE loc_13 (!{LPtr} (LocInfoE loc_14 ("queue")))) at{struct_queue} "head"))) ;
        locinfo: loc_5 ;
        Return (LocInfoE loc_6 (use{LPtr} (LocInfoE loc_7 ("queue"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [is_empty]. *)
  Definition impl_is_empty : function := {|
    f_args := [
      ("q", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_27 ;
        expr: (LocInfoE loc_38 (&(LocInfoE loc_40 (!{LPtr} (LocInfoE loc_41 ((LocInfoE loc_42 (!{LPtr} (LocInfoE loc_44 (!{LPtr} (LocInfoE loc_45 ("q")))))) at{struct_queue} "tail")))))) ;
        locinfo: loc_29 ;
        Return (LocInfoE loc_30 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_30 ((LocInfoE loc_31 (use{LPtr} (LocInfoE loc_32 ((LocInfoE loc_33 (!{LPtr} (LocInfoE loc_35 (!{LPtr} (LocInfoE loc_36 ("q")))))) at{struct_queue} "head")))) !={PtrOp, PtrOp} (LocInfoE loc_37 (NULL))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [enqueue]. *)
  Definition impl_enqueue (alloc : loc): function := {|
    f_args := [
      ("q", LPtr);
      ("v", LPtr)
    ];
    f_local_vars := [
      ("elem", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_80 ;
        "$0" <- LocInfoE loc_82 (alloc) with
          [ LocInfoE loc_83 (i2v (layout_of struct_queue_elem).(ly_size) size_t) ] ;
        "elem" <-{ LPtr }
          LocInfoE loc_80 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_80 ("$0"))) ;
        locinfo: loc_49 ;
        LocInfoE loc_75 ((LocInfoE loc_76 (!{LPtr} (LocInfoE loc_77 ("elem")))) at{struct_queue_elem} "elem") <-{ LPtr }
          LocInfoE loc_78 (use{LPtr} (LocInfoE loc_79 ("v"))) ;
        locinfo: loc_50 ;
        LocInfoE loc_71 ((LocInfoE loc_72 (!{LPtr} (LocInfoE loc_73 ("elem")))) at{struct_queue_elem} "next") <-{ LPtr }
          LocInfoE loc_74 (NULL) ;
        locinfo: loc_51 ;
        LocInfoE loc_63 (!{LPtr} (LocInfoE loc_64 ((LocInfoE loc_65 (!{LPtr} (LocInfoE loc_67 (!{LPtr} (LocInfoE loc_68 ("q")))))) at{struct_queue} "tail"))) <-{ LPtr }
          LocInfoE loc_69 (use{LPtr} (LocInfoE loc_70 ("elem"))) ;
        locinfo: loc_52 ;
        LocInfoE loc_53 ((LocInfoE loc_54 (!{LPtr} (LocInfoE loc_56 (!{LPtr} (LocInfoE loc_57 ("q")))))) at{struct_queue} "tail") <-{ LPtr }
          LocInfoE loc_58 (&(LocInfoE loc_59 ((LocInfoE loc_60 (!{LPtr} (LocInfoE loc_61 ("elem")))) at{struct_queue_elem} "next"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [dequeue]. *)
  Definition impl_dequeue (free : loc): function := {|
    f_args := [
      ("q", LPtr)
    ];
    f_local_vars := [
      ("elem", LPtr);
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_88 ;
        expr: (LocInfoE loc_166 (&(LocInfoE loc_168 (!{LPtr} (LocInfoE loc_169 ((LocInfoE loc_170 (!{LPtr} (LocInfoE loc_172 (!{LPtr} (LocInfoE loc_173 ("q")))))) at{struct_queue} "tail")))))) ;
        locinfo: loc_158 ;
        if: LocInfoE loc_158 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_158 ((LocInfoE loc_159 (use{LPtr} (LocInfoE loc_160 ((LocInfoE loc_161 (!{LPtr} (LocInfoE loc_163 (!{LPtr} (LocInfoE loc_164 ("q")))))) at{struct_queue} "head")))) ={PtrOp, PtrOp} (LocInfoE loc_165 (NULL)))))
        then
        locinfo: loc_155 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#1" :=
        "elem" <-{ LPtr }
          LocInfoE loc_146 (use{LPtr} (LocInfoE loc_147 ((LocInfoE loc_148 (!{LPtr} (LocInfoE loc_150 (!{LPtr} (LocInfoE loc_151 ("q")))))) at{struct_queue} "head"))) ;
        "ret" <-{ LPtr }
          LocInfoE loc_140 (use{LPtr} (LocInfoE loc_141 ((LocInfoE loc_142 (!{LPtr} (LocInfoE loc_143 ("elem")))) at{struct_queue_elem} "elem"))) ;
        locinfo: loc_134 ;
        if: LocInfoE loc_134 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_134 ((LocInfoE loc_135 (use{LPtr} (LocInfoE loc_136 ((LocInfoE loc_137 (!{LPtr} (LocInfoE loc_138 ("elem")))) at{struct_queue_elem} "next")))) ={PtrOp, PtrOp} (LocInfoE loc_139 (NULL)))))
        then
        locinfo: loc_104 ;
          Goto "#3"
        else
        locinfo: loc_124 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_94 ;
        "_" <- LocInfoE loc_99 (free) with
          [ LocInfoE loc_100 (i2v (layout_of struct_queue_elem).(ly_size) size_t) ;
          LocInfoE loc_101 (use{LPtr} (LocInfoE loc_102 ("elem"))) ] ;
        locinfo: loc_95 ;
        Return (LocInfoE loc_96 (use{LPtr} (LocInfoE loc_97 ("ret"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_104 ;
        LocInfoE loc_117 ((LocInfoE loc_118 (!{LPtr} (LocInfoE loc_120 (!{LPtr} (LocInfoE loc_121 ("q")))))) at{struct_queue} "head") <-{ LPtr }
          LocInfoE loc_122 (NULL) ;
        locinfo: loc_105 ;
        LocInfoE loc_106 ((LocInfoE loc_107 (!{LPtr} (LocInfoE loc_109 (!{LPtr} (LocInfoE loc_110 ("q")))))) at{struct_queue} "tail") <-{ LPtr }
          LocInfoE loc_111 (&(LocInfoE loc_112 ((LocInfoE loc_113 (!{LPtr} (LocInfoE loc_115 (!{LPtr} (LocInfoE loc_116 ("q")))))) at{struct_queue} "head"))) ;
        locinfo: loc_94 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_124 ;
        LocInfoE loc_125 ((LocInfoE loc_126 (!{LPtr} (LocInfoE loc_128 (!{LPtr} (LocInfoE loc_129 ("q")))))) at{struct_queue} "head") <-{ LPtr }
          LocInfoE loc_130 (use{LPtr} (LocInfoE loc_131 ((LocInfoE loc_132 (!{LPtr} (LocInfoE loc_133 ("elem")))) at{struct_queue_elem} "next"))) ;
        locinfo: loc_94 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_155 ;
        Return (LocInfoE loc_156 (NULL))
      ]> $
      <[ "#6" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
