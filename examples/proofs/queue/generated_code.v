From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/queue.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 27 2 27 46.
  Definition loc_12 : location_info := LocationInfo file_1 28 2 28 31.
  Definition loc_13 : location_info := LocationInfo file_1 29 2 29 29.
  Definition loc_14 : location_info := LocationInfo file_1 30 2 30 15.
  Definition loc_15 : location_info := LocationInfo file_1 30 9 30 14.
  Definition loc_16 : location_info := LocationInfo file_1 30 9 30 14.
  Definition loc_17 : location_info := LocationInfo file_1 29 2 29 13.
  Definition loc_18 : location_info := LocationInfo file_1 29 2 29 7.
  Definition loc_19 : location_info := LocationInfo file_1 29 2 29 7.
  Definition loc_20 : location_info := LocationInfo file_1 29 16 29 28.
  Definition loc_21 : location_info := LocationInfo file_1 29 17 29 28.
  Definition loc_22 : location_info := LocationInfo file_1 29 17 29 22.
  Definition loc_23 : location_info := LocationInfo file_1 29 17 29 22.
  Definition loc_24 : location_info := LocationInfo file_1 28 2 28 13.
  Definition loc_25 : location_info := LocationInfo file_1 28 2 28 7.
  Definition loc_26 : location_info := LocationInfo file_1 28 2 28 7.
  Definition loc_27 : location_info := LocationInfo file_1 28 16 28 30.
  Definition loc_28 : location_info := LocationInfo file_1 27 18 27 45.
  Definition loc_29 : location_info := LocationInfo file_1 27 18 27 23.
  Definition loc_30 : location_info := LocationInfo file_1 27 18 27 23.
  Definition loc_31 : location_info := LocationInfo file_1 27 24 27 44.
  Definition loc_36 : location_info := LocationInfo file_1 38 2 38 38.
  Definition loc_37 : location_info := LocationInfo file_1 38 9 38 37.
  Definition loc_38 : location_info := LocationInfo file_1 38 9 38 19.
  Definition loc_39 : location_info := LocationInfo file_1 38 9 38 19.
  Definition loc_40 : location_info := LocationInfo file_1 38 9 38 13.
  Definition loc_41 : location_info := LocationInfo file_1 38 9 38 13.
  Definition loc_42 : location_info := LocationInfo file_1 38 11 38 12.
  Definition loc_43 : location_info := LocationInfo file_1 38 11 38 12.
  Definition loc_44 : location_info := LocationInfo file_1 38 23 38 37.
  Definition loc_47 : location_info := LocationInfo file_1 46 2 46 55.
  Definition loc_48 : location_info := LocationInfo file_1 47 2 47 17.
  Definition loc_49 : location_info := LocationInfo file_1 48 2 48 30.
  Definition loc_50 : location_info := LocationInfo file_1 49 2 49 21.
  Definition loc_51 : location_info := LocationInfo file_1 50 2 50 27.
  Definition loc_52 : location_info := LocationInfo file_1 50 2 50 12.
  Definition loc_53 : location_info := LocationInfo file_1 50 2 50 6.
  Definition loc_54 : location_info := LocationInfo file_1 50 2 50 6.
  Definition loc_55 : location_info := LocationInfo file_1 50 4 50 5.
  Definition loc_56 : location_info := LocationInfo file_1 50 4 50 5.
  Definition loc_57 : location_info := LocationInfo file_1 50 15 50 26.
  Definition loc_58 : location_info := LocationInfo file_1 50 16 50 26.
  Definition loc_59 : location_info := LocationInfo file_1 50 16 50 20.
  Definition loc_60 : location_info := LocationInfo file_1 50 16 50 20.
  Definition loc_61 : location_info := LocationInfo file_1 49 2 49 13.
  Definition loc_62 : location_info := LocationInfo file_1 49 3 49 13.
  Definition loc_63 : location_info := LocationInfo file_1 49 3 49 13.
  Definition loc_64 : location_info := LocationInfo file_1 49 3 49 7.
  Definition loc_65 : location_info := LocationInfo file_1 49 3 49 7.
  Definition loc_66 : location_info := LocationInfo file_1 49 5 49 6.
  Definition loc_67 : location_info := LocationInfo file_1 49 5 49 6.
  Definition loc_68 : location_info := LocationInfo file_1 49 16 49 20.
  Definition loc_69 : location_info := LocationInfo file_1 49 16 49 20.
  Definition loc_70 : location_info := LocationInfo file_1 48 2 48 12.
  Definition loc_71 : location_info := LocationInfo file_1 48 2 48 6.
  Definition loc_72 : location_info := LocationInfo file_1 48 2 48 6.
  Definition loc_73 : location_info := LocationInfo file_1 48 15 48 29.
  Definition loc_74 : location_info := LocationInfo file_1 47 2 47 12.
  Definition loc_75 : location_info := LocationInfo file_1 47 2 47 6.
  Definition loc_76 : location_info := LocationInfo file_1 47 2 47 6.
  Definition loc_77 : location_info := LocationInfo file_1 47 15 47 16.
  Definition loc_78 : location_info := LocationInfo file_1 47 15 47 16.
  Definition loc_79 : location_info := LocationInfo file_1 46 22 46 54.
  Definition loc_80 : location_info := LocationInfo file_1 46 22 46 27.
  Definition loc_81 : location_info := LocationInfo file_1 46 22 46 27.
  Definition loc_82 : location_info := LocationInfo file_1 46 28 46 53.
  Definition loc_87 : location_info := LocationInfo file_1 59 2 61 3.
  Definition loc_88 : location_info := LocationInfo file_1 62 2 62 33.
  Definition loc_89 : location_info := LocationInfo file_1 63 2 63 25.
  Definition loc_90 : location_info := LocationInfo file_1 64 2 69 3.
  Definition loc_91 : location_info := LocationInfo file_1 70 2 70 40.
  Definition loc_92 : location_info := LocationInfo file_1 71 2 71 13.
  Definition loc_93 : location_info := LocationInfo file_1 71 9 71 12.
  Definition loc_94 : location_info := LocationInfo file_1 71 9 71 12.
  Definition loc_95 : location_info := LocationInfo file_1 70 2 70 6.
  Definition loc_96 : location_info := LocationInfo file_1 70 2 70 6.
  Definition loc_97 : location_info := LocationInfo file_1 70 7 70 32.
  Definition loc_98 : location_info := LocationInfo file_1 70 34 70 38.
  Definition loc_99 : location_info := LocationInfo file_1 70 34 70 38.
  Definition loc_100 : location_info := LocationInfo file_1 64 35 67 3.
  Definition loc_101 : location_info := LocationInfo file_1 65 4 65 32.
  Definition loc_102 : location_info := LocationInfo file_1 66 4 66 29.
  Definition loc_103 : location_info := LocationInfo file_1 66 4 66 14.
  Definition loc_104 : location_info := LocationInfo file_1 66 4 66 8.
  Definition loc_105 : location_info := LocationInfo file_1 66 4 66 8.
  Definition loc_106 : location_info := LocationInfo file_1 66 6 66 7.
  Definition loc_107 : location_info := LocationInfo file_1 66 6 66 7.
  Definition loc_108 : location_info := LocationInfo file_1 66 17 66 28.
  Definition loc_109 : location_info := LocationInfo file_1 66 18 66 28.
  Definition loc_110 : location_info := LocationInfo file_1 66 18 66 22.
  Definition loc_111 : location_info := LocationInfo file_1 66 18 66 22.
  Definition loc_112 : location_info := LocationInfo file_1 66 20 66 21.
  Definition loc_113 : location_info := LocationInfo file_1 66 20 66 21.
  Definition loc_114 : location_info := LocationInfo file_1 65 4 65 14.
  Definition loc_115 : location_info := LocationInfo file_1 65 4 65 8.
  Definition loc_116 : location_info := LocationInfo file_1 65 4 65 8.
  Definition loc_117 : location_info := LocationInfo file_1 65 6 65 7.
  Definition loc_118 : location_info := LocationInfo file_1 65 6 65 7.
  Definition loc_119 : location_info := LocationInfo file_1 65 17 65 31.
  Definition loc_120 : location_info := LocationInfo file_1 67 9 69 3.
  Definition loc_121 : location_info := LocationInfo file_1 68 4 68 28.
  Definition loc_122 : location_info := LocationInfo file_1 68 4 68 14.
  Definition loc_123 : location_info := LocationInfo file_1 68 4 68 8.
  Definition loc_124 : location_info := LocationInfo file_1 68 4 68 8.
  Definition loc_125 : location_info := LocationInfo file_1 68 6 68 7.
  Definition loc_126 : location_info := LocationInfo file_1 68 6 68 7.
  Definition loc_127 : location_info := LocationInfo file_1 68 17 68 27.
  Definition loc_128 : location_info := LocationInfo file_1 68 17 68 27.
  Definition loc_129 : location_info := LocationInfo file_1 68 17 68 21.
  Definition loc_130 : location_info := LocationInfo file_1 68 17 68 21.
  Definition loc_131 : location_info := LocationInfo file_1 64 5 64 33.
  Definition loc_132 : location_info := LocationInfo file_1 64 5 64 15.
  Definition loc_133 : location_info := LocationInfo file_1 64 5 64 15.
  Definition loc_134 : location_info := LocationInfo file_1 64 5 64 9.
  Definition loc_135 : location_info := LocationInfo file_1 64 5 64 9.
  Definition loc_136 : location_info := LocationInfo file_1 64 19 64 33.
  Definition loc_137 : location_info := LocationInfo file_1 63 14 63 24.
  Definition loc_138 : location_info := LocationInfo file_1 63 14 63 24.
  Definition loc_139 : location_info := LocationInfo file_1 63 14 63 18.
  Definition loc_140 : location_info := LocationInfo file_1 63 14 63 18.
  Definition loc_143 : location_info := LocationInfo file_1 62 22 62 32.
  Definition loc_144 : location_info := LocationInfo file_1 62 22 62 32.
  Definition loc_145 : location_info := LocationInfo file_1 62 22 62 26.
  Definition loc_146 : location_info := LocationInfo file_1 62 22 62 26.
  Definition loc_147 : location_info := LocationInfo file_1 62 24 62 25.
  Definition loc_148 : location_info := LocationInfo file_1 62 24 62 25.
  Definition loc_151 : location_info := LocationInfo file_1 59 36 61 3.
  Definition loc_152 : location_info := LocationInfo file_1 60 4 60 26.
  Definition loc_153 : location_info := LocationInfo file_1 60 11 60 25.
  Definition loc_155 : location_info := LocationInfo file_1 59 6 59 34.
  Definition loc_156 : location_info := LocationInfo file_1 59 6 59 16.
  Definition loc_157 : location_info := LocationInfo file_1 59 6 59 16.
  Definition loc_158 : location_info := LocationInfo file_1 59 6 59 10.
  Definition loc_159 : location_info := LocationInfo file_1 59 6 59 10.
  Definition loc_160 : location_info := LocationInfo file_1 59 8 59 9.
  Definition loc_161 : location_info := LocationInfo file_1 59 8 59 9.
  Definition loc_162 : location_info := LocationInfo file_1 59 20 59 34.

  (* Definition of struct [queue_elem]. *)
  Program Definition struct_queue_elem := {|
    sl_members := [
      (Some "elem", void*);
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [queue]. *)
  Program Definition struct_queue := {|
    sl_members := [
      (Some "head", void*);
      (Some "tail", void*)
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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_queue]. *)
  Definition impl_init_queue (global_alloc : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("queue", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "queue" <-{ void* }
          LocInfoE loc_28 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_28 (Call (LocInfoE loc_30 (global_alloc)) [@{expr} LocInfoE loc_31 (i2v (layout_of struct_queue).(ly_size) size_t) ]))) ;
        locinfo: loc_12 ;
        LocInfoE loc_24 ((LocInfoE loc_25 (!{void*} (LocInfoE loc_26 ("queue")))) at{struct_queue} "head") <-{ void* }
          LocInfoE loc_27 (NULL) ;
        locinfo: loc_13 ;
        LocInfoE loc_17 ((LocInfoE loc_18 (!{void*} (LocInfoE loc_19 ("queue")))) at{struct_queue} "tail") <-{ void* }
          LocInfoE loc_20 (&(LocInfoE loc_21 ((LocInfoE loc_22 (!{void*} (LocInfoE loc_23 ("queue")))) at{struct_queue} "head"))) ;
        locinfo: loc_14 ;
        Return (LocInfoE loc_15 (use{void*} (LocInfoE loc_16 ("queue"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [is_empty]. *)
  Definition impl_is_empty : function := {|
    f_args := [
      ("q", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_36 ;
        Return (LocInfoE loc_37 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_37 ((LocInfoE loc_38 (use{void*} (LocInfoE loc_39 ((LocInfoE loc_40 (!{void*} (LocInfoE loc_42 (!{void*} (LocInfoE loc_43 ("q")))))) at{struct_queue} "head")))) !={PtrOp, PtrOp} (LocInfoE loc_44 (NULL))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [enqueue]. *)
  Definition impl_enqueue (global_alloc : loc): function := {|
    f_args := [
      ("q", void*);
      ("v", void*)
    ];
    f_local_vars := [
      ("elem", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "elem" <-{ void* }
          LocInfoE loc_79 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_79 (Call (LocInfoE loc_81 (global_alloc)) [@{expr} LocInfoE loc_82 (i2v (layout_of struct_queue_elem).(ly_size) size_t) ]))) ;
        locinfo: loc_48 ;
        LocInfoE loc_74 ((LocInfoE loc_75 (!{void*} (LocInfoE loc_76 ("elem")))) at{struct_queue_elem} "elem") <-{ void* }
          LocInfoE loc_77 (use{void*} (LocInfoE loc_78 ("v"))) ;
        locinfo: loc_49 ;
        LocInfoE loc_70 ((LocInfoE loc_71 (!{void*} (LocInfoE loc_72 ("elem")))) at{struct_queue_elem} "next") <-{ void* }
          LocInfoE loc_73 (NULL) ;
        locinfo: loc_50 ;
        LocInfoE loc_62 (!{void*} (LocInfoE loc_63 ((LocInfoE loc_64 (!{void*} (LocInfoE loc_66 (!{void*} (LocInfoE loc_67 ("q")))))) at{struct_queue} "tail"))) <-{ void* }
          LocInfoE loc_68 (use{void*} (LocInfoE loc_69 ("elem"))) ;
        locinfo: loc_51 ;
        LocInfoE loc_52 ((LocInfoE loc_53 (!{void*} (LocInfoE loc_55 (!{void*} (LocInfoE loc_56 ("q")))))) at{struct_queue} "tail") <-{ void* }
          LocInfoE loc_57 (&(LocInfoE loc_58 ((LocInfoE loc_59 (!{void*} (LocInfoE loc_60 ("elem")))) at{struct_queue_elem} "next"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [dequeue]. *)
  Definition impl_dequeue (global_free : loc): function := {|
    f_args := [
      ("q", void*)
    ];
    f_local_vars := [
      ("elem", void*);
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_155 ;
        if: LocInfoE loc_155 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_155 ((LocInfoE loc_156 (use{void*} (LocInfoE loc_157 ((LocInfoE loc_158 (!{void*} (LocInfoE loc_160 (!{void*} (LocInfoE loc_161 ("q")))))) at{struct_queue} "head")))) ={PtrOp, PtrOp} (LocInfoE loc_162 (NULL)))))
        then
        locinfo: loc_152 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#1" :=
        "elem" <-{ void* }
          LocInfoE loc_143 (use{void*} (LocInfoE loc_144 ((LocInfoE loc_145 (!{void*} (LocInfoE loc_147 (!{void*} (LocInfoE loc_148 ("q")))))) at{struct_queue} "head"))) ;
        "ret" <-{ void* }
          LocInfoE loc_137 (use{void*} (LocInfoE loc_138 ((LocInfoE loc_139 (!{void*} (LocInfoE loc_140 ("elem")))) at{struct_queue_elem} "elem"))) ;
        locinfo: loc_131 ;
        if: LocInfoE loc_131 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_131 ((LocInfoE loc_132 (use{void*} (LocInfoE loc_133 ((LocInfoE loc_134 (!{void*} (LocInfoE loc_135 ("elem")))) at{struct_queue_elem} "next")))) ={PtrOp, PtrOp} (LocInfoE loc_136 (NULL)))))
        then
        locinfo: loc_101 ;
          Goto "#3"
        else
        locinfo: loc_121 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_91 ;
        expr: (LocInfoE loc_91 (Call (LocInfoE loc_96 (global_free)) [@{expr} LocInfoE loc_97 (i2v (layout_of struct_queue_elem).(ly_size) size_t) ;
        LocInfoE loc_98 (use{void*} (LocInfoE loc_99 ("elem"))) ])) ;
        locinfo: loc_92 ;
        Return (LocInfoE loc_93 (use{void*} (LocInfoE loc_94 ("ret"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_101 ;
        LocInfoE loc_114 ((LocInfoE loc_115 (!{void*} (LocInfoE loc_117 (!{void*} (LocInfoE loc_118 ("q")))))) at{struct_queue} "head") <-{ void* }
          LocInfoE loc_119 (NULL) ;
        locinfo: loc_102 ;
        LocInfoE loc_103 ((LocInfoE loc_104 (!{void*} (LocInfoE loc_106 (!{void*} (LocInfoE loc_107 ("q")))))) at{struct_queue} "tail") <-{ void* }
          LocInfoE loc_108 (&(LocInfoE loc_109 ((LocInfoE loc_110 (!{void*} (LocInfoE loc_112 (!{void*} (LocInfoE loc_113 ("q")))))) at{struct_queue} "head"))) ;
        locinfo: loc_91 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_121 ;
        LocInfoE loc_122 ((LocInfoE loc_123 (!{void*} (LocInfoE loc_125 (!{void*} (LocInfoE loc_126 ("q")))))) at{struct_queue} "head") <-{ void* }
          LocInfoE loc_127 (use{void*} (LocInfoE loc_128 ((LocInfoE loc_129 (!{void*} (LocInfoE loc_130 ("elem")))) at{struct_queue_elem} "next"))) ;
        locinfo: loc_91 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_152 ;
        Return (LocInfoE loc_153 (NULL))
      ]> $
      <[ "#6" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
