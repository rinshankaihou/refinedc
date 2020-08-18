From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/misc.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/misc.c".
  Definition loc_2 : location_info := LocationInfo file_0 17 2 19 3.
  Definition loc_3 : location_info := LocationInfo file_0 20 2 20 17.
  Definition loc_4 : location_info := LocationInfo file_0 21 2 21 28.
  Definition loc_5 : location_info := LocationInfo file_0 21 9 21 27.
  Definition loc_6 : location_info := LocationInfo file_0 21 9 21 18.
  Definition loc_7 : location_info := LocationInfo file_0 21 9 21 18.
  Definition loc_8 : location_info := LocationInfo file_0 21 9 21 10.
  Definition loc_9 : location_info := LocationInfo file_0 21 9 21 10.
  Definition loc_10 : location_info := LocationInfo file_0 21 21 21 27.
  Definition loc_11 : location_info := LocationInfo file_0 21 21 21 27.
  Definition loc_12 : location_info := LocationInfo file_0 21 21 21 22.
  Definition loc_13 : location_info := LocationInfo file_0 21 21 21 22.
  Definition loc_14 : location_info := LocationInfo file_0 20 2 20 8.
  Definition loc_15 : location_info := LocationInfo file_0 20 2 20 3.
  Definition loc_16 : location_info := LocationInfo file_0 20 2 20 3.
  Definition loc_17 : location_info := LocationInfo file_0 20 2 20 16.
  Definition loc_18 : location_info := LocationInfo file_0 20 2 20 8.
  Definition loc_19 : location_info := LocationInfo file_0 20 2 20 8.
  Definition loc_20 : location_info := LocationInfo file_0 20 2 20 3.
  Definition loc_21 : location_info := LocationInfo file_0 20 2 20 3.
  Definition loc_22 : location_info := LocationInfo file_0 20 12 20 16.
  Definition loc_23 : location_info := LocationInfo file_0 20 12 20 16.
  Definition loc_24 : location_info := LocationInfo file_0 17 20 19 3.
  Definition loc_25 : location_info := LocationInfo file_0 18 4 18 26.
  Definition loc_26 : location_info := LocationInfo file_0 18 11 18 25.
  Definition loc_28 : location_info := LocationInfo file_0 17 5 17 18.
  Definition loc_29 : location_info := LocationInfo file_0 17 5 17 9.
  Definition loc_30 : location_info := LocationInfo file_0 17 5 17 9.
  Definition loc_31 : location_info := LocationInfo file_0 17 12 17 18.
  Definition loc_32 : location_info := LocationInfo file_0 17 12 17 18.
  Definition loc_33 : location_info := LocationInfo file_0 17 12 17 13.
  Definition loc_34 : location_info := LocationInfo file_0 17 12 17 13.
  Definition loc_37 : location_info := LocationInfo file_0 37 2 37 17.
  Definition loc_38 : location_info := LocationInfo file_0 38 2 38 35.
  Definition loc_39 : location_info := LocationInfo file_0 38 35 38 3.
  Definition loc_40 : location_info := LocationInfo file_0 39 2 39 33.
  Definition loc_41 : location_info := LocationInfo file_0 40 2 40 19.
  Definition loc_42 : location_info := LocationInfo file_0 41 2 41 13.
  Definition loc_43 : location_info := LocationInfo file_0 41 9 41 12.
  Definition loc_44 : location_info := LocationInfo file_0 41 9 41 12.
  Definition loc_45 : location_info := LocationInfo file_0 40 2 40 11.
  Definition loc_46 : location_info := LocationInfo file_0 40 2 40 11.
  Definition loc_47 : location_info := LocationInfo file_0 40 12 40 17.
  Definition loc_48 : location_info := LocationInfo file_0 40 13 40 17.
  Definition loc_49 : location_info := LocationInfo file_0 39 14 39 32.
  Definition loc_50 : location_info := LocationInfo file_0 39 14 39 19.
  Definition loc_51 : location_info := LocationInfo file_0 39 14 39 19.
  Definition loc_52 : location_info := LocationInfo file_0 39 20 39 25.
  Definition loc_53 : location_info := LocationInfo file_0 39 21 39 25.
  Definition loc_54 : location_info := LocationInfo file_0 39 27 39 31.
  Definition loc_55 : location_info := LocationInfo file_0 39 27 39 31.
  Definition loc_58 : location_info := LocationInfo file_0 38 27 38 34.
  Definition loc_59 : location_info := LocationInfo file_0 38 28 38 34.
  Definition loc_60 : location_info := LocationInfo file_0 37 2 37 9.
  Definition loc_61 : location_info := LocationInfo file_0 37 2 37 9.
  Definition loc_62 : location_info := LocationInfo file_0 37 10 37 15.
  Definition loc_63 : location_info := LocationInfo file_0 37 11 37 15.
  Definition loc_66 : location_info := LocationInfo file_0 62 2 62 23.
  Definition loc_67 : location_info := LocationInfo file_0 66 2 69 3.
  Definition loc_68 : location_info := LocationInfo file_0 70 2 70 24.
  Definition loc_69 : location_info := LocationInfo file_0 71 2 71 21.
  Definition loc_70 : location_info := LocationInfo file_0 72 2 72 21.
  Definition loc_71 : location_info := LocationInfo file_0 73 2 73 15.
  Definition loc_72 : location_info := LocationInfo file_0 73 2 73 6.
  Definition loc_73 : location_info := LocationInfo file_0 73 3 73 6.
  Definition loc_74 : location_info := LocationInfo file_0 73 3 73 6.
  Definition loc_75 : location_info := LocationInfo file_0 73 9 73 14.
  Definition loc_76 : location_info := LocationInfo file_0 73 9 73 14.
  Definition loc_77 : location_info := LocationInfo file_0 72 2 72 13.
  Definition loc_78 : location_info := LocationInfo file_0 72 2 72 7.
  Definition loc_79 : location_info := LocationInfo file_0 72 2 72 7.
  Definition loc_80 : location_info := LocationInfo file_0 72 16 72 20.
  Definition loc_81 : location_info := LocationInfo file_0 72 16 72 20.
  Definition loc_82 : location_info := LocationInfo file_0 72 17 72 20.
  Definition loc_83 : location_info := LocationInfo file_0 72 17 72 20.
  Definition loc_84 : location_info := LocationInfo file_0 71 2 71 13.
  Definition loc_85 : location_info := LocationInfo file_0 71 2 71 7.
  Definition loc_86 : location_info := LocationInfo file_0 71 2 71 7.
  Definition loc_87 : location_info := LocationInfo file_0 71 16 71 20.
  Definition loc_88 : location_info := LocationInfo file_0 71 16 71 20.
  Definition loc_89 : location_info := LocationInfo file_0 70 19 70 23.
  Definition loc_90 : location_info := LocationInfo file_0 70 19 70 23.
  Definition loc_93 : location_info := LocationInfo file_0 66 2 69 3.
  Definition loc_94 : location_info := LocationInfo file_0 66 32 69 3.
  Definition loc_95 : location_info := LocationInfo file_0 67 4 67 35.
  Definition loc_96 : location_info := LocationInfo file_0 68 4 68 24.
  Definition loc_97 : location_info := LocationInfo file_0 66 2 69 3.
  Definition loc_98 : location_info := LocationInfo file_0 66 2 69 3.
  Definition loc_99 : location_info := LocationInfo file_0 68 4 68 7.
  Definition loc_100 : location_info := LocationInfo file_0 68 10 68 23.
  Definition loc_101 : location_info := LocationInfo file_0 68 11 68 23.
  Definition loc_102 : location_info := LocationInfo file_0 68 11 68 17.
  Definition loc_103 : location_info := LocationInfo file_0 68 11 68 17.
  Definition loc_104 : location_info := LocationInfo file_0 68 13 68 16.
  Definition loc_105 : location_info := LocationInfo file_0 68 13 68 16.
  Definition loc_106 : location_info := LocationInfo file_0 67 29 67 35.
  Definition loc_108 : location_info := LocationInfo file_0 67 7 67 27.
  Definition loc_109 : location_info := LocationInfo file_0 67 7 67 11.
  Definition loc_110 : location_info := LocationInfo file_0 67 7 67 11.
  Definition loc_111 : location_info := LocationInfo file_0 67 15 67 27.
  Definition loc_112 : location_info := LocationInfo file_0 67 15 67 27.
  Definition loc_113 : location_info := LocationInfo file_0 67 15 67 21.
  Definition loc_114 : location_info := LocationInfo file_0 67 15 67 21.
  Definition loc_115 : location_info := LocationInfo file_0 67 17 67 20.
  Definition loc_116 : location_info := LocationInfo file_0 67 17 67 20.
  Definition loc_117 : location_info := LocationInfo file_0 66 8 66 30.
  Definition loc_118 : location_info := LocationInfo file_0 66 8 66 12.
  Definition loc_119 : location_info := LocationInfo file_0 66 8 66 12.
  Definition loc_120 : location_info := LocationInfo file_0 66 9 66 12.
  Definition loc_121 : location_info := LocationInfo file_0 66 9 66 12.
  Definition loc_122 : location_info := LocationInfo file_0 66 16 66 30.
  Definition loc_123 : location_info := LocationInfo file_0 62 18 62 22.
  Definition loc_124 : location_info := LocationInfo file_0 62 18 62 22.
  Definition loc_129 : location_info := LocationInfo file_0 88 2 88 24.
  Definition loc_130 : location_info := LocationInfo file_0 89 2 89 30.
  Definition loc_131 : location_info := LocationInfo file_0 89 2 89 19.
  Definition loc_132 : location_info := LocationInfo file_0 89 2 89 19.
  Definition loc_133 : location_info := LocationInfo file_0 89 20 89 28.
  Definition loc_134 : location_info := LocationInfo file_0 89 20 89 28.
  Definition loc_135 : location_info := LocationInfo file_0 89 21 89 28.
  Definition loc_136 : location_info := LocationInfo file_0 89 21 89 28.
  Definition loc_137 : location_info := LocationInfo file_0 88 20 88 23.
  Definition loc_138 : location_info := LocationInfo file_0 88 20 88 23.
  Definition loc_143 : location_info := LocationInfo file_0 98 2 98 12.
  Definition loc_144 : location_info := LocationInfo file_0 99 2 99 47.
  Definition loc_145 : location_info := LocationInfo file_0 100 2 100 23.
  Definition loc_146 : location_info := LocationInfo file_0 100 2 100 19.
  Definition loc_147 : location_info := LocationInfo file_0 100 2 100 19.
  Definition loc_148 : location_info := LocationInfo file_0 100 20 100 21.
  Definition loc_149 : location_info := LocationInfo file_0 99 2 99 6.
  Definition loc_150 : location_info := LocationInfo file_0 99 2 99 6.
  Definition loc_151 : location_info := LocationInfo file_0 99 7 99 37.
  Definition loc_152 : location_info := LocationInfo file_0 99 39 99 45.
  Definition loc_153 : location_info := LocationInfo file_0 99 40 99 45.
  Definition loc_154 : location_info := LocationInfo file_0 98 2 98 7.
  Definition loc_155 : location_info := LocationInfo file_0 98 10 98 11.

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

  (* Definition of struct [alloc_data]. *)
  Program Definition struct_alloc_data := {|
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
        locinfo: loc_28 ;
        if: LocInfoE loc_28 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_28 ((LocInfoE loc_29 (use{it_layout size_t} (LocInfoE loc_30 ("size")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_31 (use{it_layout size_t} (LocInfoE loc_32 ((LocInfoE loc_33 (!{LPtr} (LocInfoE loc_34 ("d")))) at{struct_alloc_data} "len")))))))
        then
        locinfo: loc_25 ;
          Goto "#2"
        else
        locinfo: loc_3 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_3 ;
        LocInfoE loc_14 ((LocInfoE loc_15 (!{LPtr} (LocInfoE loc_16 ("d")))) at{struct_alloc_data} "len") <-{ it_layout size_t }
          LocInfoE loc_17 ((LocInfoE loc_18 (use{it_layout size_t} (LocInfoE loc_19 ((LocInfoE loc_20 (!{LPtr} (LocInfoE loc_21 ("d")))) at{struct_alloc_data} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_22 (use{it_layout size_t} (LocInfoE loc_23 ("size"))))) ;
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 ((LocInfoE loc_6 (use{LPtr} (LocInfoE loc_7 ((LocInfoE loc_8 (!{LPtr} (LocInfoE loc_9 ("d")))) at{struct_alloc_data} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_10 (use{it_layout size_t} (LocInfoE loc_11 ((LocInfoE loc_12 (!{LPtr} (LocInfoE loc_13 ("d")))) at{struct_alloc_data} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [thread_safe_alloc]. *)
  Definition impl_thread_safe_alloc (lock data sl_lock sl_unlock alloc : loc): function := {|
    f_args := [
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_37 ;
        "_" <- LocInfoE loc_61 (sl_lock) with
          [ LocInfoE loc_62 (&(LocInfoE loc_63 (lock))) ] ;
        locinfo: loc_38 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_58 (&(LocInfoE loc_59 (data)))) ;
        locinfo: loc_49 ;
        "$0" <- LocInfoE loc_51 (alloc) with
          [ LocInfoE loc_52 (&(LocInfoE loc_53 (data))) ;
          LocInfoE loc_54 (use{it_layout size_t} (LocInfoE loc_55 ("size"))) ] ;
        "ret" <-{ LPtr } LocInfoE loc_49 ("$0") ;
        locinfo: loc_41 ;
        "_" <- LocInfoE loc_46 (sl_unlock) with
          [ LocInfoE loc_47 (AnnotExpr 1%nat LockA (LocInfoE loc_47 (&(LocInfoE loc_48 (lock))))) ] ;
        locinfo: loc_42 ;
        Return (LocInfoE loc_43 (use{LPtr} (LocInfoE loc_44 ("ret"))))
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
          LocInfoE loc_123 (use{LPtr} (LocInfoE loc_124 ("list"))) ;
        locinfo: loc_67 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_117 ;
        if: LocInfoE loc_117 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_117 ((LocInfoE loc_118 (use{LPtr} (LocInfoE loc_120 (!{LPtr} (LocInfoE loc_121 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_122 (NULL)))))
        then
        locinfo: loc_108 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_108 ;
        if: LocInfoE loc_108 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_108 ((LocInfoE loc_109 (use{it_layout size_t} (LocInfoE loc_110 ("size")))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_111 (use{it_layout size_t} (LocInfoE loc_112 ((LocInfoE loc_113 (!{LPtr} (LocInfoE loc_115 (!{LPtr} (LocInfoE loc_116 ("cur")))))) at{struct_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_96 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        "entry" <-{ LPtr }
          LocInfoE loc_89 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_89 (use{LPtr} (LocInfoE loc_90 ("data"))))) ;
        locinfo: loc_69 ;
        LocInfoE loc_84 ((LocInfoE loc_85 (!{LPtr} (LocInfoE loc_86 ("entry")))) at{struct_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_87 (use{it_layout size_t} (LocInfoE loc_88 ("size"))) ;
        locinfo: loc_70 ;
        LocInfoE loc_77 ((LocInfoE loc_78 (!{LPtr} (LocInfoE loc_79 ("entry")))) at{struct_chunk} "next") <-{ LPtr }
          LocInfoE loc_80 (use{LPtr} (LocInfoE loc_82 (!{LPtr} (LocInfoE loc_83 ("cur"))))) ;
        locinfo: loc_71 ;
        LocInfoE loc_73 (!{LPtr} (LocInfoE loc_74 ("cur"))) <-{ LPtr }
          LocInfoE loc_75 (use{LPtr} (LocInfoE loc_76 ("entry"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_96 ;
        LocInfoE loc_99 ("cur") <-{ LPtr }
          LocInfoE loc_100 (&(LocInfoE loc_101 ((LocInfoE loc_102 (!{LPtr} (LocInfoE loc_104 (!{LPtr} (LocInfoE loc_105 ("cur")))))) at{struct_chunk} "next"))) ;
        locinfo: loc_97 ;
        Goto "continue7"
      ]> $
      <[ "#5" :=
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_96 ;
        Goto "#4"
      ]> $
      <[ "continue7" :=
        locinfo: loc_67 ;
        Goto "#1"
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
          LocInfoE loc_137 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_137 (use{LPtr} (LocInfoE loc_138 ("num"))))) ;
        locinfo: loc_130 ;
        "_" <- LocInfoE loc_132 (thread_safe_alloc) with
          [ LocInfoE loc_133 (use{it_layout size_t} (LocInfoE loc_135 (!{LPtr} (LocInfoE loc_136 ("num_int"))))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_thread_safe_alloc]. *)
  Definition impl_test_thread_safe_alloc (param thread_safe_alloc fork test_thread_safe_alloc_fork_fn : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_143 ;
        LocInfoE loc_154 (param) <-{ it_layout size_t }
          LocInfoE loc_155 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_155 (i2v 5 i32))) ;
        locinfo: loc_144 ;
        "_" <- LocInfoE loc_150 (fork) with
          [ LocInfoE loc_151 (test_thread_safe_alloc_fork_fn) ;
          LocInfoE loc_152 (&(LocInfoE loc_153 (param))) ] ;
        locinfo: loc_145 ;
        "_" <- LocInfoE loc_147 (thread_safe_alloc) with
          [ LocInfoE loc_148 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_148 (i2v 5 i32))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
