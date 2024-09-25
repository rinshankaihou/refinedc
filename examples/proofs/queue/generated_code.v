From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section code.
  Definition file_0 : string := "include/assume.h".
  Definition file_1 : string := "examples/queue.c".
  Definition file_2 : string := "include/refinedc.h".
  Definition file_3 : string := "include/refinedc_malloc.h".
  Definition loc_2 : location_info := LocationInfo file_2 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_2 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_2 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_2 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_2 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_2 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_2 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_0 10 2 10 12.
  Definition loc_12 : location_info := LocationInfo file_0 15 2 15 11.
  Definition loc_13 : location_info := LocationInfo file_0 15 9 15 10.
  Definition loc_14 : location_info := LocationInfo file_0 10 10 10 12.
  Definition loc_15 : location_info := LocationInfo file_0 10 8 10 9.
  Definition loc_18 : location_info := LocationInfo file_3 33 2 33 23.
  Definition loc_19 : location_info := LocationInfo file_3 34 2 34 42.
  Definition loc_20 : location_info := LocationInfo file_3 35 2 35 11.
  Definition loc_21 : location_info := LocationInfo file_3 35 9 35 10.
  Definition loc_22 : location_info := LocationInfo file_3 35 9 35 10.
  Definition loc_23 : location_info := LocationInfo file_3 34 26 34 42.
  Definition loc_24 : location_info := LocationInfo file_3 34 28 34 40.
  Definition loc_25 : location_info := LocationInfo file_3 34 28 34 37.
  Definition loc_26 : location_info := LocationInfo file_3 34 28 34 37.
  Definition loc_27 : location_info := LocationInfo file_3 34 2 34 42.
  Definition loc_28 : location_info := LocationInfo file_3 34 5 34 24.
  Definition loc_29 : location_info := LocationInfo file_3 34 5 34 6.
  Definition loc_30 : location_info := LocationInfo file_3 34 5 34 6.
  Definition loc_31 : location_info := LocationInfo file_3 34 10 34 24.
  Definition loc_32 : location_info := LocationInfo file_3 33 12 33 22.
  Definition loc_33 : location_info := LocationInfo file_3 33 12 33 18.
  Definition loc_34 : location_info := LocationInfo file_3 33 12 33 18.
  Definition loc_35 : location_info := LocationInfo file_3 33 19 33 21.
  Definition loc_36 : location_info := LocationInfo file_3 33 19 33 21.
  Definition loc_41 : location_info := LocationInfo file_1 26 2 26 48.
  Definition loc_42 : location_info := LocationInfo file_1 27 2 27 31.
  Definition loc_43 : location_info := LocationInfo file_1 28 2 28 29.
  Definition loc_44 : location_info := LocationInfo file_1 29 2 29 15.
  Definition loc_45 : location_info := LocationInfo file_1 29 9 29 14.
  Definition loc_46 : location_info := LocationInfo file_1 29 9 29 14.
  Definition loc_47 : location_info := LocationInfo file_1 28 2 28 13.
  Definition loc_48 : location_info := LocationInfo file_1 28 2 28 7.
  Definition loc_49 : location_info := LocationInfo file_1 28 2 28 7.
  Definition loc_50 : location_info := LocationInfo file_1 28 16 28 28.
  Definition loc_51 : location_info := LocationInfo file_1 28 17 28 28.
  Definition loc_52 : location_info := LocationInfo file_1 28 17 28 22.
  Definition loc_53 : location_info := LocationInfo file_1 28 17 28 22.
  Definition loc_54 : location_info := LocationInfo file_1 27 2 27 13.
  Definition loc_55 : location_info := LocationInfo file_1 27 2 27 7.
  Definition loc_56 : location_info := LocationInfo file_1 27 2 27 7.
  Definition loc_57 : location_info := LocationInfo file_1 27 16 27 30.
  Definition loc_58 : location_info := LocationInfo file_1 26 18 26 47.
  Definition loc_59 : location_info := LocationInfo file_1 26 18 26 25.
  Definition loc_60 : location_info := LocationInfo file_1 26 18 26 25.
  Definition loc_61 : location_info := LocationInfo file_1 26 26 26 46.
  Definition loc_66 : location_info := LocationInfo file_1 37 2 37 38.
  Definition loc_67 : location_info := LocationInfo file_1 37 9 37 37.
  Definition loc_68 : location_info := LocationInfo file_1 37 9 37 19.
  Definition loc_69 : location_info := LocationInfo file_1 37 9 37 19.
  Definition loc_70 : location_info := LocationInfo file_1 37 9 37 13.
  Definition loc_71 : location_info := LocationInfo file_1 37 9 37 13.
  Definition loc_72 : location_info := LocationInfo file_1 37 11 37 12.
  Definition loc_73 : location_info := LocationInfo file_1 37 11 37 12.
  Definition loc_74 : location_info := LocationInfo file_1 37 23 37 37.
  Definition loc_77 : location_info := LocationInfo file_1 44 2 44 57.
  Definition loc_78 : location_info := LocationInfo file_1 45 2 45 17.
  Definition loc_79 : location_info := LocationInfo file_1 46 2 46 30.
  Definition loc_80 : location_info := LocationInfo file_1 47 2 47 21.
  Definition loc_81 : location_info := LocationInfo file_1 48 2 48 27.
  Definition loc_82 : location_info := LocationInfo file_1 48 2 48 12.
  Definition loc_83 : location_info := LocationInfo file_1 48 2 48 6.
  Definition loc_84 : location_info := LocationInfo file_1 48 2 48 6.
  Definition loc_85 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_86 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_87 : location_info := LocationInfo file_1 48 15 48 26.
  Definition loc_88 : location_info := LocationInfo file_1 48 16 48 26.
  Definition loc_89 : location_info := LocationInfo file_1 48 16 48 20.
  Definition loc_90 : location_info := LocationInfo file_1 48 16 48 20.
  Definition loc_91 : location_info := LocationInfo file_1 47 2 47 13.
  Definition loc_92 : location_info := LocationInfo file_1 47 3 47 13.
  Definition loc_93 : location_info := LocationInfo file_1 47 3 47 13.
  Definition loc_94 : location_info := LocationInfo file_1 47 3 47 7.
  Definition loc_95 : location_info := LocationInfo file_1 47 3 47 7.
  Definition loc_96 : location_info := LocationInfo file_1 47 5 47 6.
  Definition loc_97 : location_info := LocationInfo file_1 47 5 47 6.
  Definition loc_98 : location_info := LocationInfo file_1 47 16 47 20.
  Definition loc_99 : location_info := LocationInfo file_1 47 16 47 20.
  Definition loc_100 : location_info := LocationInfo file_1 46 2 46 12.
  Definition loc_101 : location_info := LocationInfo file_1 46 2 46 6.
  Definition loc_102 : location_info := LocationInfo file_1 46 2 46 6.
  Definition loc_103 : location_info := LocationInfo file_1 46 15 46 29.
  Definition loc_104 : location_info := LocationInfo file_1 45 2 45 12.
  Definition loc_105 : location_info := LocationInfo file_1 45 2 45 6.
  Definition loc_106 : location_info := LocationInfo file_1 45 2 45 6.
  Definition loc_107 : location_info := LocationInfo file_1 45 15 45 16.
  Definition loc_108 : location_info := LocationInfo file_1 45 15 45 16.
  Definition loc_109 : location_info := LocationInfo file_1 44 22 44 56.
  Definition loc_110 : location_info := LocationInfo file_1 44 22 44 29.
  Definition loc_111 : location_info := LocationInfo file_1 44 22 44 29.
  Definition loc_112 : location_info := LocationInfo file_1 44 30 44 55.
  Definition loc_117 : location_info := LocationInfo file_1 56 2 58 3.
  Definition loc_118 : location_info := LocationInfo file_1 59 2 59 33.
  Definition loc_119 : location_info := LocationInfo file_1 60 2 60 25.
  Definition loc_120 : location_info := LocationInfo file_1 61 2 66 3.
  Definition loc_121 : location_info := LocationInfo file_1 67 2 67 13.
  Definition loc_122 : location_info := LocationInfo file_1 68 2 68 13.
  Definition loc_123 : location_info := LocationInfo file_1 68 9 68 12.
  Definition loc_124 : location_info := LocationInfo file_1 68 9 68 12.
  Definition loc_125 : location_info := LocationInfo file_1 67 2 67 6.
  Definition loc_126 : location_info := LocationInfo file_1 67 2 67 6.
  Definition loc_127 : location_info := LocationInfo file_1 67 7 67 11.
  Definition loc_128 : location_info := LocationInfo file_1 67 7 67 11.
  Definition loc_129 : location_info := LocationInfo file_1 61 35 64 3.
  Definition loc_130 : location_info := LocationInfo file_1 62 4 62 32.
  Definition loc_131 : location_info := LocationInfo file_1 63 4 63 29.
  Definition loc_132 : location_info := LocationInfo file_1 63 4 63 14.
  Definition loc_133 : location_info := LocationInfo file_1 63 4 63 8.
  Definition loc_134 : location_info := LocationInfo file_1 63 4 63 8.
  Definition loc_135 : location_info := LocationInfo file_1 63 6 63 7.
  Definition loc_136 : location_info := LocationInfo file_1 63 6 63 7.
  Definition loc_137 : location_info := LocationInfo file_1 63 17 63 28.
  Definition loc_138 : location_info := LocationInfo file_1 63 18 63 28.
  Definition loc_139 : location_info := LocationInfo file_1 63 18 63 22.
  Definition loc_140 : location_info := LocationInfo file_1 63 18 63 22.
  Definition loc_141 : location_info := LocationInfo file_1 63 20 63 21.
  Definition loc_142 : location_info := LocationInfo file_1 63 20 63 21.
  Definition loc_143 : location_info := LocationInfo file_1 62 4 62 14.
  Definition loc_144 : location_info := LocationInfo file_1 62 4 62 8.
  Definition loc_145 : location_info := LocationInfo file_1 62 4 62 8.
  Definition loc_146 : location_info := LocationInfo file_1 62 6 62 7.
  Definition loc_147 : location_info := LocationInfo file_1 62 6 62 7.
  Definition loc_148 : location_info := LocationInfo file_1 62 17 62 31.
  Definition loc_149 : location_info := LocationInfo file_1 64 9 66 3.
  Definition loc_150 : location_info := LocationInfo file_1 65 4 65 28.
  Definition loc_151 : location_info := LocationInfo file_1 65 4 65 14.
  Definition loc_152 : location_info := LocationInfo file_1 65 4 65 8.
  Definition loc_153 : location_info := LocationInfo file_1 65 4 65 8.
  Definition loc_154 : location_info := LocationInfo file_1 65 6 65 7.
  Definition loc_155 : location_info := LocationInfo file_1 65 6 65 7.
  Definition loc_156 : location_info := LocationInfo file_1 65 17 65 27.
  Definition loc_157 : location_info := LocationInfo file_1 65 17 65 27.
  Definition loc_158 : location_info := LocationInfo file_1 65 17 65 21.
  Definition loc_159 : location_info := LocationInfo file_1 65 17 65 21.
  Definition loc_160 : location_info := LocationInfo file_1 61 5 61 33.
  Definition loc_161 : location_info := LocationInfo file_1 61 5 61 15.
  Definition loc_162 : location_info := LocationInfo file_1 61 5 61 15.
  Definition loc_163 : location_info := LocationInfo file_1 61 5 61 9.
  Definition loc_164 : location_info := LocationInfo file_1 61 5 61 9.
  Definition loc_165 : location_info := LocationInfo file_1 61 19 61 33.
  Definition loc_166 : location_info := LocationInfo file_1 60 14 60 24.
  Definition loc_167 : location_info := LocationInfo file_1 60 14 60 24.
  Definition loc_168 : location_info := LocationInfo file_1 60 14 60 18.
  Definition loc_169 : location_info := LocationInfo file_1 60 14 60 18.
  Definition loc_172 : location_info := LocationInfo file_1 59 22 59 32.
  Definition loc_173 : location_info := LocationInfo file_1 59 22 59 32.
  Definition loc_174 : location_info := LocationInfo file_1 59 22 59 26.
  Definition loc_175 : location_info := LocationInfo file_1 59 22 59 26.
  Definition loc_176 : location_info := LocationInfo file_1 59 24 59 25.
  Definition loc_177 : location_info := LocationInfo file_1 59 24 59 25.
  Definition loc_180 : location_info := LocationInfo file_1 56 36 58 3.
  Definition loc_181 : location_info := LocationInfo file_1 57 4 57 26.
  Definition loc_182 : location_info := LocationInfo file_1 57 11 57 25.
  Definition loc_183 : location_info := LocationInfo file_1 56 2 58 3.
  Definition loc_184 : location_info := LocationInfo file_1 56 6 56 34.
  Definition loc_185 : location_info := LocationInfo file_1 56 6 56 16.
  Definition loc_186 : location_info := LocationInfo file_1 56 6 56 16.
  Definition loc_187 : location_info := LocationInfo file_1 56 6 56 10.
  Definition loc_188 : location_info := LocationInfo file_1 56 6 56 10.
  Definition loc_189 : location_info := LocationInfo file_1 56 8 56 9.
  Definition loc_190 : location_info := LocationInfo file_1 56 8 56 9.
  Definition loc_191 : location_info := LocationInfo file_1 56 20 56 34.

  (* Definition of struct [__cerbty_unnamed_tag_520]. *)
  Program Definition struct___cerbty_unnamed_tag_520 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{IntOp uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{PtrOp} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [safe_exit]. *)
  Definition impl_safe_exit : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_15 ;
        if{IntOp i32, None}: LocInfoE loc_15 (i2v 1 i32)
        then
        locinfo: loc_11 ;
          Goto "#2"
        else
        locinfo: loc_12 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [xmalloc]. *)
  Definition impl_xmalloc (global_malloc global_safe_exit : loc): function := {|
    f_args := [
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
      ("p", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "p" <-{ PtrOp }
          LocInfoE loc_32 (Call (LocInfoE loc_34 (global_malloc)) [@{expr} LocInfoE loc_35 (use{IntOp size_t} (LocInfoE loc_36 ("sz"))) ]) ;
        locinfo: loc_28 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_28 ((LocInfoE loc_29 (use{PtrOp} (LocInfoE loc_30 ("p")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_31 (NULL)))
        then
        locinfo: loc_24 ;
          Goto "#2"
        else
        locinfo: loc_20 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_20 ;
        Return (LocInfoE loc_21 (use{PtrOp} (LocInfoE loc_22 ("p"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_24 ;
        expr: (LocInfoE loc_24 (Call (LocInfoE loc_26 (global_safe_exit)) [@{expr}  ])) ;
        locinfo: loc_20 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_20 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_queue]. *)
  Definition impl_init_queue (global_xmalloc : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("queue", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "queue" <-{ PtrOp }
          LocInfoE loc_58 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_58 (Call (LocInfoE loc_60 (global_xmalloc)) [@{expr} LocInfoE loc_61 (i2v (layout_of struct_queue).(ly_size) size_t) ]))) ;
        locinfo: loc_42 ;
        LocInfoE loc_54 ((LocInfoE loc_55 (!{PtrOp} (LocInfoE loc_56 ("queue")))) at{struct_queue} "head") <-{ PtrOp }
          LocInfoE loc_57 (NULL) ;
        locinfo: loc_43 ;
        LocInfoE loc_47 ((LocInfoE loc_48 (!{PtrOp} (LocInfoE loc_49 ("queue")))) at{struct_queue} "tail") <-{ PtrOp }
          LocInfoE loc_50 (&(LocInfoE loc_51 ((LocInfoE loc_52 (!{PtrOp} (LocInfoE loc_53 ("queue")))) at{struct_queue} "head"))) ;
        locinfo: loc_44 ;
        Return (LocInfoE loc_45 (use{PtrOp} (LocInfoE loc_46 ("queue"))))
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
        locinfo: loc_66 ;
        Return (LocInfoE loc_67 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_67 ((LocInfoE loc_68 (use{PtrOp} (LocInfoE loc_69 ((LocInfoE loc_70 (!{PtrOp} (LocInfoE loc_72 (!{PtrOp} (LocInfoE loc_73 ("q")))))) at{struct_queue} "head")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_74 (NULL))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [enqueue]. *)
  Definition impl_enqueue (global_xmalloc : loc): function := {|
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
        "elem" <-{ PtrOp }
          LocInfoE loc_109 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_109 (Call (LocInfoE loc_111 (global_xmalloc)) [@{expr} LocInfoE loc_112 (i2v (layout_of struct_queue_elem).(ly_size) size_t) ]))) ;
        locinfo: loc_78 ;
        LocInfoE loc_104 ((LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("elem")))) at{struct_queue_elem} "elem") <-{ PtrOp }
          LocInfoE loc_107 (use{PtrOp} (LocInfoE loc_108 ("v"))) ;
        locinfo: loc_79 ;
        LocInfoE loc_100 ((LocInfoE loc_101 (!{PtrOp} (LocInfoE loc_102 ("elem")))) at{struct_queue_elem} "next") <-{ PtrOp }
          LocInfoE loc_103 (NULL) ;
        locinfo: loc_80 ;
        LocInfoE loc_92 (!{PtrOp} (LocInfoE loc_93 ((LocInfoE loc_94 (!{PtrOp} (LocInfoE loc_96 (!{PtrOp} (LocInfoE loc_97 ("q")))))) at{struct_queue} "tail"))) <-{ PtrOp }
          LocInfoE loc_98 (use{PtrOp} (LocInfoE loc_99 ("elem"))) ;
        locinfo: loc_81 ;
        LocInfoE loc_82 ((LocInfoE loc_83 (!{PtrOp} (LocInfoE loc_85 (!{PtrOp} (LocInfoE loc_86 ("q")))))) at{struct_queue} "tail") <-{ PtrOp }
          LocInfoE loc_87 (&(LocInfoE loc_88 ((LocInfoE loc_89 (!{PtrOp} (LocInfoE loc_90 ("elem")))) at{struct_queue_elem} "next"))) ;
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
        locinfo: loc_184 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_184 ((LocInfoE loc_185 (use{PtrOp} (LocInfoE loc_186 ((LocInfoE loc_187 (!{PtrOp} (LocInfoE loc_189 (!{PtrOp} (LocInfoE loc_190 ("q")))))) at{struct_queue} "head")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_191 (NULL)))
        then
        locinfo: loc_181 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#1" :=
        "elem" <-{ PtrOp }
          LocInfoE loc_172 (use{PtrOp} (LocInfoE loc_173 ((LocInfoE loc_174 (!{PtrOp} (LocInfoE loc_176 (!{PtrOp} (LocInfoE loc_177 ("q")))))) at{struct_queue} "head"))) ;
        "ret" <-{ PtrOp }
          LocInfoE loc_166 (use{PtrOp} (LocInfoE loc_167 ((LocInfoE loc_168 (!{PtrOp} (LocInfoE loc_169 ("elem")))) at{struct_queue_elem} "elem"))) ;
        locinfo: loc_160 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_160 ((LocInfoE loc_161 (use{PtrOp} (LocInfoE loc_162 ((LocInfoE loc_163 (!{PtrOp} (LocInfoE loc_164 ("elem")))) at{struct_queue_elem} "next")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_165 (NULL)))
        then
        locinfo: loc_130 ;
          Goto "#3"
        else
        locinfo: loc_150 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_121 ;
        expr: (LocInfoE loc_121 (Call (LocInfoE loc_126 (global_free)) [@{expr} LocInfoE loc_127 (use{PtrOp} (LocInfoE loc_128 ("elem"))) ])) ;
        locinfo: loc_122 ;
        Return (LocInfoE loc_123 (use{PtrOp} (LocInfoE loc_124 ("ret"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_130 ;
        LocInfoE loc_143 ((LocInfoE loc_144 (!{PtrOp} (LocInfoE loc_146 (!{PtrOp} (LocInfoE loc_147 ("q")))))) at{struct_queue} "head") <-{ PtrOp }
          LocInfoE loc_148 (NULL) ;
        locinfo: loc_131 ;
        LocInfoE loc_132 ((LocInfoE loc_133 (!{PtrOp} (LocInfoE loc_135 (!{PtrOp} (LocInfoE loc_136 ("q")))))) at{struct_queue} "tail") <-{ PtrOp }
          LocInfoE loc_137 (&(LocInfoE loc_138 ((LocInfoE loc_139 (!{PtrOp} (LocInfoE loc_141 (!{PtrOp} (LocInfoE loc_142 ("q")))))) at{struct_queue} "head"))) ;
        locinfo: loc_121 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_150 ;
        LocInfoE loc_151 ((LocInfoE loc_152 (!{PtrOp} (LocInfoE loc_154 (!{PtrOp} (LocInfoE loc_155 ("q")))))) at{struct_queue} "head") <-{ PtrOp }
          LocInfoE loc_156 (use{PtrOp} (LocInfoE loc_157 ((LocInfoE loc_158 (!{PtrOp} (LocInfoE loc_159 ("elem")))) at{struct_queue_elem} "next"))) ;
        locinfo: loc_121 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_181 ;
        Return (LocInfoE loc_182 (NULL))
      ]> $
      <[ "#6" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
