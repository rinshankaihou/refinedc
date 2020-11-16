From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section code.
  Definition file_0 : string := "examples/paper_examples.c".
  Definition loc_2 : location_info := LocationInfo file_0 29 2 29 42.
  Definition loc_3 : location_info := LocationInfo file_0 30 2 30 17.
  Definition loc_4 : location_info := LocationInfo file_0 31 2 31 28.
  Definition loc_5 : location_info := LocationInfo file_0 31 9 31 27.
  Definition loc_6 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_7 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_8 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_9 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_10 : location_info := LocationInfo file_0 31 21 31 27.
  Definition loc_11 : location_info := LocationInfo file_0 31 21 31 27.
  Definition loc_12 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_13 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_14 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_15 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_16 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_17 : location_info := LocationInfo file_0 30 2 30 16.
  Definition loc_18 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_19 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_20 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_21 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_22 : location_info := LocationInfo file_0 30 12 30 16.
  Definition loc_23 : location_info := LocationInfo file_0 30 12 30 16.
  Definition loc_24 : location_info := LocationInfo file_0 29 20 29 42.
  Definition loc_25 : location_info := LocationInfo file_0 29 27 29 41.
  Definition loc_27 : location_info := LocationInfo file_0 29 5 29 18.
  Definition loc_28 : location_info := LocationInfo file_0 29 5 29 9.
  Definition loc_29 : location_info := LocationInfo file_0 29 5 29 9.
  Definition loc_30 : location_info := LocationInfo file_0 29 12 29 18.
  Definition loc_31 : location_info := LocationInfo file_0 29 12 29 18.
  Definition loc_32 : location_info := LocationInfo file_0 29 12 29 13.
  Definition loc_33 : location_info := LocationInfo file_0 29 12 29 13.
  Definition loc_36 : location_info := LocationInfo file_0 58 2 58 23.
  Definition loc_37 : location_info := LocationInfo file_0 64 2 67 3.
  Definition loc_38 : location_info := LocationInfo file_0 68 2 68 24.
  Definition loc_39 : location_info := LocationInfo file_0 69 2 69 21.
  Definition loc_40 : location_info := LocationInfo file_0 70 2 70 21.
  Definition loc_41 : location_info := LocationInfo file_0 71 2 71 15.
  Definition loc_42 : location_info := LocationInfo file_0 71 2 71 6.
  Definition loc_43 : location_info := LocationInfo file_0 71 3 71 6.
  Definition loc_44 : location_info := LocationInfo file_0 71 3 71 6.
  Definition loc_45 : location_info := LocationInfo file_0 71 9 71 14.
  Definition loc_46 : location_info := LocationInfo file_0 71 9 71 14.
  Definition loc_47 : location_info := LocationInfo file_0 70 2 70 13.
  Definition loc_48 : location_info := LocationInfo file_0 70 2 70 7.
  Definition loc_49 : location_info := LocationInfo file_0 70 2 70 7.
  Definition loc_50 : location_info := LocationInfo file_0 70 16 70 20.
  Definition loc_51 : location_info := LocationInfo file_0 70 16 70 20.
  Definition loc_52 : location_info := LocationInfo file_0 70 17 70 20.
  Definition loc_53 : location_info := LocationInfo file_0 70 17 70 20.
  Definition loc_54 : location_info := LocationInfo file_0 69 2 69 13.
  Definition loc_55 : location_info := LocationInfo file_0 69 2 69 7.
  Definition loc_56 : location_info := LocationInfo file_0 69 2 69 7.
  Definition loc_57 : location_info := LocationInfo file_0 69 16 69 20.
  Definition loc_58 : location_info := LocationInfo file_0 69 16 69 20.
  Definition loc_59 : location_info := LocationInfo file_0 68 19 68 23.
  Definition loc_60 : location_info := LocationInfo file_0 68 19 68 23.
  Definition loc_63 : location_info := LocationInfo file_0 64 2 67 3.
  Definition loc_64 : location_info := LocationInfo file_0 64 32 67 3.
  Definition loc_65 : location_info := LocationInfo file_0 65 4 65 35.
  Definition loc_66 : location_info := LocationInfo file_0 66 4 66 24.
  Definition loc_67 : location_info := LocationInfo file_0 64 2 67 3.
  Definition loc_68 : location_info := LocationInfo file_0 64 2 67 3.
  Definition loc_69 : location_info := LocationInfo file_0 66 4 66 7.
  Definition loc_70 : location_info := LocationInfo file_0 66 10 66 23.
  Definition loc_71 : location_info := LocationInfo file_0 66 11 66 23.
  Definition loc_72 : location_info := LocationInfo file_0 66 11 66 17.
  Definition loc_73 : location_info := LocationInfo file_0 66 11 66 17.
  Definition loc_74 : location_info := LocationInfo file_0 66 13 66 16.
  Definition loc_75 : location_info := LocationInfo file_0 66 13 66 16.
  Definition loc_76 : location_info := LocationInfo file_0 65 29 65 35.
  Definition loc_78 : location_info := LocationInfo file_0 65 7 65 27.
  Definition loc_79 : location_info := LocationInfo file_0 65 7 65 11.
  Definition loc_80 : location_info := LocationInfo file_0 65 7 65 11.
  Definition loc_81 : location_info := LocationInfo file_0 65 15 65 27.
  Definition loc_82 : location_info := LocationInfo file_0 65 15 65 27.
  Definition loc_83 : location_info := LocationInfo file_0 65 15 65 21.
  Definition loc_84 : location_info := LocationInfo file_0 65 15 65 21.
  Definition loc_85 : location_info := LocationInfo file_0 65 17 65 20.
  Definition loc_86 : location_info := LocationInfo file_0 65 17 65 20.
  Definition loc_87 : location_info := LocationInfo file_0 64 8 64 30.
  Definition loc_88 : location_info := LocationInfo file_0 64 8 64 12.
  Definition loc_89 : location_info := LocationInfo file_0 64 8 64 12.
  Definition loc_90 : location_info := LocationInfo file_0 64 9 64 12.
  Definition loc_91 : location_info := LocationInfo file_0 64 9 64 12.
  Definition loc_92 : location_info := LocationInfo file_0 64 16 64 30.
  Definition loc_93 : location_info := LocationInfo file_0 58 18 58 22.
  Definition loc_94 : location_info := LocationInfo file_0 58 18 58 22.
  Definition loc_99 : location_info := LocationInfo file_0 89 2 89 17.
  Definition loc_100 : location_info := LocationInfo file_0 90 2 90 35.
  Definition loc_101 : location_info := LocationInfo file_0 90 35 90 3.
  Definition loc_102 : location_info := LocationInfo file_0 91 2 91 33.
  Definition loc_103 : location_info := LocationInfo file_0 92 2 92 19.
  Definition loc_104 : location_info := LocationInfo file_0 93 2 93 13.
  Definition loc_105 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_106 : location_info := LocationInfo file_0 93 9 93 12.
  Definition loc_107 : location_info := LocationInfo file_0 92 2 92 11.
  Definition loc_108 : location_info := LocationInfo file_0 92 2 92 11.
  Definition loc_109 : location_info := LocationInfo file_0 92 12 92 17.
  Definition loc_110 : location_info := LocationInfo file_0 92 13 92 17.
  Definition loc_111 : location_info := LocationInfo file_0 91 14 91 32.
  Definition loc_112 : location_info := LocationInfo file_0 91 14 91 19.
  Definition loc_113 : location_info := LocationInfo file_0 91 14 91 19.
  Definition loc_114 : location_info := LocationInfo file_0 91 20 91 25.
  Definition loc_115 : location_info := LocationInfo file_0 91 21 91 25.
  Definition loc_116 : location_info := LocationInfo file_0 91 27 91 31.
  Definition loc_117 : location_info := LocationInfo file_0 91 27 91 31.
  Definition loc_120 : location_info := LocationInfo file_0 90 27 90 34.
  Definition loc_121 : location_info := LocationInfo file_0 90 28 90 34.
  Definition loc_122 : location_info := LocationInfo file_0 89 2 89 9.
  Definition loc_123 : location_info := LocationInfo file_0 89 2 89 9.
  Definition loc_124 : location_info := LocationInfo file_0 89 10 89 15.
  Definition loc_125 : location_info := LocationInfo file_0 89 11 89 15.
  Definition loc_128 : location_info := LocationInfo file_0 107 2 107 10.
  Definition loc_129 : location_info := LocationInfo file_0 107 2 107 4.
  Definition loc_130 : location_info := LocationInfo file_0 107 2 107 4.
  Definition loc_131 : location_info := LocationInfo file_0 107 2 107 4.
  Definition loc_132 : location_info := LocationInfo file_0 107 5 107 8.
  Definition loc_133 : location_info := LocationInfo file_0 107 5 107 8.
  Definition loc_136 : location_info := LocationInfo file_0 113 2 113 24.
  Definition loc_137 : location_info := LocationInfo file_0 114 2 114 30.
  Definition loc_138 : location_info := LocationInfo file_0 114 2 114 19.
  Definition loc_139 : location_info := LocationInfo file_0 114 2 114 19.
  Definition loc_140 : location_info := LocationInfo file_0 114 20 114 28.
  Definition loc_141 : location_info := LocationInfo file_0 114 20 114 28.
  Definition loc_142 : location_info := LocationInfo file_0 114 21 114 28.
  Definition loc_143 : location_info := LocationInfo file_0 114 21 114 28.
  Definition loc_144 : location_info := LocationInfo file_0 113 20 113 23.
  Definition loc_145 : location_info := LocationInfo file_0 113 20 113 23.
  Definition loc_150 : location_info := LocationInfo file_0 123 2 123 12.
  Definition loc_151 : location_info := LocationInfo file_0 124 2 124 47.
  Definition loc_152 : location_info := LocationInfo file_0 125 2 125 23.
  Definition loc_153 : location_info := LocationInfo file_0 125 2 125 19.
  Definition loc_154 : location_info := LocationInfo file_0 125 2 125 19.
  Definition loc_155 : location_info := LocationInfo file_0 125 20 125 21.
  Definition loc_156 : location_info := LocationInfo file_0 124 2 124 6.
  Definition loc_157 : location_info := LocationInfo file_0 124 2 124 6.
  Definition loc_158 : location_info := LocationInfo file_0 124 7 124 37.
  Definition loc_159 : location_info := LocationInfo file_0 124 39 124 45.
  Definition loc_160 : location_info := LocationInfo file_0 124 40 124 45.
  Definition loc_161 : location_info := LocationInfo file_0 123 2 123 7.
  Definition loc_162 : location_info := LocationInfo file_0 123 10 123 11.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mem_t]. *)
  Program Definition struct_mem_t := {|
    sl_members := [
      (Some "len", it_layout size_t);
      (Some "buffer", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [chunk]. *)
  Program Definition struct_chunk := {|
    sl_members := [
      (Some "size", it_layout size_t);
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [alloc]. *)
  Definition impl_alloc : function := {|
    f_args := [
      ("d", LPtr);
      ("size", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_27 ;
        if: LocInfoE loc_27 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_27 ((LocInfoE loc_28 (use{it_layout size_t} (LocInfoE loc_29 ("size")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_30 (use{it_layout size_t} (LocInfoE loc_31 ((LocInfoE loc_32 (!{LPtr} (LocInfoE loc_33 ("d")))) at{struct_mem_t} "len")))))))
        then
        locinfo: loc_24 ;
          Goto "#2"
        else
        locinfo: loc_3 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_3 ;
        LocInfoE loc_14 ((LocInfoE loc_15 (!{LPtr} (LocInfoE loc_16 ("d")))) at{struct_mem_t} "len") <-{ it_layout size_t }
          LocInfoE loc_17 ((LocInfoE loc_18 (use{it_layout size_t} (LocInfoE loc_19 ((LocInfoE loc_20 (!{LPtr} (LocInfoE loc_21 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_22 (use{it_layout size_t} (LocInfoE loc_23 ("size"))))) ;
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 ((LocInfoE loc_6 (use{LPtr} (LocInfoE loc_7 ((LocInfoE loc_8 (!{LPtr} (LocInfoE loc_9 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_10 (use{it_layout size_t} (LocInfoE loc_11 ((LocInfoE loc_12 (!{LPtr} (LocInfoE loc_13 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_24 ;
        Return (LocInfoE loc_25 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [free]. *)
  Definition impl_free : function := {|
    f_args := [
      ("list", LPtr);
      ("data", LPtr);
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("cur", LPtr);
      ("entry", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ LPtr }
          LocInfoE loc_93 (use{LPtr} (LocInfoE loc_94 ("list"))) ;
        locinfo: loc_37 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_87 ;
        if: LocInfoE loc_87 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_87 ((LocInfoE loc_88 (use{LPtr} (LocInfoE loc_90 (!{LPtr} (LocInfoE loc_91 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_92 (NULL)))))
        then
        locinfo: loc_78 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_78 ;
        if: LocInfoE loc_78 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_78 ((LocInfoE loc_79 (use{it_layout size_t} (LocInfoE loc_80 ("size")))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_81 (use{it_layout size_t} (LocInfoE loc_82 ((LocInfoE loc_83 (!{LPtr} (LocInfoE loc_85 (!{LPtr} (LocInfoE loc_86 ("cur")))))) at{struct_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_66 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        "entry" <-{ LPtr }
          LocInfoE loc_59 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_59 (use{LPtr} (LocInfoE loc_60 ("data"))))) ;
        locinfo: loc_39 ;
        LocInfoE loc_54 ((LocInfoE loc_55 (!{LPtr} (LocInfoE loc_56 ("entry")))) at{struct_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_57 (use{it_layout size_t} (LocInfoE loc_58 ("size"))) ;
        locinfo: loc_40 ;
        LocInfoE loc_47 ((LocInfoE loc_48 (!{LPtr} (LocInfoE loc_49 ("entry")))) at{struct_chunk} "next") <-{ LPtr }
          LocInfoE loc_50 (use{LPtr} (LocInfoE loc_52 (!{LPtr} (LocInfoE loc_53 ("cur"))))) ;
        locinfo: loc_41 ;
        LocInfoE loc_43 (!{LPtr} (LocInfoE loc_44 ("cur"))) <-{ LPtr }
          LocInfoE loc_45 (use{LPtr} (LocInfoE loc_46 ("entry"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_66 ;
        LocInfoE loc_69 ("cur") <-{ LPtr }
          LocInfoE loc_70 (&(LocInfoE loc_71 ((LocInfoE loc_72 (!{LPtr} (LocInfoE loc_74 (!{LPtr} (LocInfoE loc_75 ("cur")))))) at{struct_chunk} "next"))) ;
        locinfo: loc_67 ;
        Goto "continue4"
      ]> $
      <[ "#5" :=
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_66 ;
        Goto "#4"
      ]> $
      <[ "continue4" :=
        locinfo: loc_37 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [thread_safe_alloc]. *)
  Definition impl_thread_safe_alloc (data lock alloc sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_99 ;
        "_" <- LocInfoE loc_123 (sl_lock) with
          [ LocInfoE loc_124 (&(LocInfoE loc_125 (lock))) ] ;
        locinfo: loc_100 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_120 (&(LocInfoE loc_121 (data)))) ;
        locinfo: loc_111 ;
        "$0" <- LocInfoE loc_113 (alloc) with
          [ LocInfoE loc_114 (&(LocInfoE loc_115 (data))) ;
          LocInfoE loc_116 (use{it_layout size_t} (LocInfoE loc_117 ("size"))) ] ;
        "ret" <-{ LPtr } LocInfoE loc_111 ("$0") ;
        locinfo: loc_103 ;
        "_" <- LocInfoE loc_108 (sl_unlock) with
          [ LocInfoE loc_109 (AnnotExpr 1%nat LockA (LocInfoE loc_109 (&(LocInfoE loc_110 (lock))))) ] ;
        locinfo: loc_104 ;
        Return (LocInfoE loc_105 (use{LPtr} (LocInfoE loc_106 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fork]. *)
  Definition impl_fork : function := {|
    f_args := [
      ("fn", LPtr);
      ("arg", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_128 ;
        "_" <- LocInfoE loc_130 (use{LPtr} (LocInfoE loc_131 ("fn"))) with
          [ LocInfoE loc_132 (use{LPtr} (LocInfoE loc_133 ("arg"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_thread_safe_alloc_fork_fn]. *)
  Definition impl_test_thread_safe_alloc_fork_fn (thread_safe_alloc : loc): function := {|
    f_args := [
      ("num", LPtr)
    ];
    f_local_vars := [
      ("num_int", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "num_int" <-{ LPtr }
          LocInfoE loc_144 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_144 (use{LPtr} (LocInfoE loc_145 ("num"))))) ;
        locinfo: loc_137 ;
        "_" <- LocInfoE loc_139 (thread_safe_alloc) with
          [ LocInfoE loc_140 (use{it_layout size_t} (LocInfoE loc_142 (!{LPtr} (LocInfoE loc_143 ("num_int"))))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_thread_safe_alloc]. *)
  Definition impl_test_thread_safe_alloc (param fork test_thread_safe_alloc_fork_fn thread_safe_alloc : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_150 ;
        LocInfoE loc_161 (param) <-{ it_layout size_t }
          LocInfoE loc_162 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_162 (i2v 5 i32))) ;
        locinfo: loc_151 ;
        "_" <- LocInfoE loc_157 (fork) with
          [ LocInfoE loc_158 (test_thread_safe_alloc_fork_fn) ;
          LocInfoE loc_159 (&(LocInfoE loc_160 (param))) ] ;
        locinfo: loc_152 ;
        "_" <- LocInfoE loc_154 (thread_safe_alloc) with
          [ LocInfoE loc_155 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_155 (i2v 5 i32))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
