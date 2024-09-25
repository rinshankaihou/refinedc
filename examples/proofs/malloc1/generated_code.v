From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/malloc1.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 47 4 47 17.
  Definition loc_12 : location_info := LocationInfo file_1 48 4 48 29.
  Definition loc_13 : location_info := LocationInfo file_1 49 4 49 31.
  Definition loc_14 : location_info := LocationInfo file_1 50 4 50 29.
  Definition loc_15 : location_info := LocationInfo file_1 50 4 50 11.
  Definition loc_16 : location_info := LocationInfo file_1 50 4 50 5.
  Definition loc_17 : location_info := LocationInfo file_1 50 4 50 5.
  Definition loc_18 : location_info := LocationInfo file_1 50 14 50 28.
  Definition loc_19 : location_info := LocationInfo file_1 49 4 49 17.
  Definition loc_20 : location_info := LocationInfo file_1 49 4 49 5.
  Definition loc_21 : location_info := LocationInfo file_1 49 4 49 5.
  Definition loc_22 : location_info := LocationInfo file_1 49 20 49 30.
  Definition loc_23 : location_info := LocationInfo file_1 49 20 49 30.
  Definition loc_24 : location_info := LocationInfo file_1 48 4 48 16.
  Definition loc_25 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_26 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_27 : location_info := LocationInfo file_1 48 19 48 28.
  Definition loc_28 : location_info := LocationInfo file_1 48 19 48 28.
  Definition loc_29 : location_info := LocationInfo file_1 47 4 47 12.
  Definition loc_30 : location_info := LocationInfo file_1 47 4 47 5.
  Definition loc_31 : location_info := LocationInfo file_1 47 4 47 5.
  Definition loc_32 : location_info := LocationInfo file_1 47 15 47 16.
  Definition loc_33 : location_info := LocationInfo file_1 47 15 47 16.
  Definition loc_36 : location_info := LocationInfo file_1 60 4 60 23.
  Definition loc_37 : location_info := LocationInfo file_1 61 4 61 12.
  Definition loc_38 : location_info := LocationInfo file_1 62 4 76 5.
  Definition loc_39 : location_info := LocationInfo file_1 62 35 67 5.
  Definition loc_40 : location_info := LocationInfo file_1 63 8 63 20.
  Definition loc_41 : location_info := LocationInfo file_1 64 8 64 26.
  Definition loc_42 : location_info := LocationInfo file_1 65 8 65 14.
  Definition loc_43 : location_info := LocationInfo file_1 66 8 66 17.
  Definition loc_44 : location_info := LocationInfo file_1 66 15 66 16.
  Definition loc_45 : location_info := LocationInfo file_1 66 15 66 16.
  Definition loc_46 : location_info := LocationInfo file_1 65 8 65 9.
  Definition loc_47 : location_info := LocationInfo file_1 65 12 65 13.
  Definition loc_48 : location_info := LocationInfo file_1 65 12 65 13.
  Definition loc_49 : location_info := LocationInfo file_1 64 8 64 15.
  Definition loc_50 : location_info := LocationInfo file_1 64 8 64 9.
  Definition loc_51 : location_info := LocationInfo file_1 64 8 64 9.
  Definition loc_52 : location_info := LocationInfo file_1 64 18 64 25.
  Definition loc_53 : location_info := LocationInfo file_1 64 18 64 25.
  Definition loc_54 : location_info := LocationInfo file_1 64 18 64 19.
  Definition loc_55 : location_info := LocationInfo file_1 64 18 64 19.
  Definition loc_56 : location_info := LocationInfo file_1 63 8 63 9.
  Definition loc_57 : location_info := LocationInfo file_1 63 12 63 19.
  Definition loc_58 : location_info := LocationInfo file_1 63 12 63 19.
  Definition loc_59 : location_info := LocationInfo file_1 63 12 63 13.
  Definition loc_60 : location_info := LocationInfo file_1 63 12 63 13.
  Definition loc_61 : location_info := LocationInfo file_1 67 11 76 5.
  Definition loc_62 : location_info := LocationInfo file_1 68 8 75 9.
  Definition loc_63 : location_info := LocationInfo file_1 68 42 70 9.
  Definition loc_64 : location_info := LocationInfo file_1 69 12 69 34.
  Definition loc_65 : location_info := LocationInfo file_1 69 19 69 33.
  Definition loc_66 : location_info := LocationInfo file_1 70 15 75 9.
  Definition loc_67 : location_info := LocationInfo file_1 71 12 71 25.
  Definition loc_68 : location_info := LocationInfo file_1 72 12 72 48.
  Definition loc_69 : location_info := LocationInfo file_1 73 12 73 56.
  Definition loc_70 : location_info := LocationInfo file_1 74 12 74 21.
  Definition loc_71 : location_info := LocationInfo file_1 74 19 74 20.
  Definition loc_72 : location_info := LocationInfo file_1 74 19 74 20.
  Definition loc_73 : location_info := LocationInfo file_1 73 12 73 24.
  Definition loc_74 : location_info := LocationInfo file_1 73 12 73 13.
  Definition loc_75 : location_info := LocationInfo file_1 73 12 73 13.
  Definition loc_76 : location_info := LocationInfo file_1 73 27 73 55.
  Definition loc_77 : location_info := LocationInfo file_1 73 27 73 39.
  Definition loc_78 : location_info := LocationInfo file_1 73 27 73 39.
  Definition loc_79 : location_info := LocationInfo file_1 73 27 73 28.
  Definition loc_80 : location_info := LocationInfo file_1 73 27 73 28.
  Definition loc_81 : location_info := LocationInfo file_1 73 42 73 55.
  Definition loc_82 : location_info := LocationInfo file_1 73 42 73 55.
  Definition loc_83 : location_info := LocationInfo file_1 73 42 73 43.
  Definition loc_84 : location_info := LocationInfo file_1 73 42 73 43.
  Definition loc_85 : location_info := LocationInfo file_1 72 12 72 20.
  Definition loc_86 : location_info := LocationInfo file_1 72 12 72 13.
  Definition loc_87 : location_info := LocationInfo file_1 72 12 72 13.
  Definition loc_88 : location_info := LocationInfo file_1 72 23 72 47.
  Definition loc_89 : location_info := LocationInfo file_1 72 23 72 31.
  Definition loc_90 : location_info := LocationInfo file_1 72 23 72 31.
  Definition loc_91 : location_info := LocationInfo file_1 72 23 72 24.
  Definition loc_92 : location_info := LocationInfo file_1 72 23 72 24.
  Definition loc_93 : location_info := LocationInfo file_1 72 34 72 47.
  Definition loc_94 : location_info := LocationInfo file_1 72 34 72 47.
  Definition loc_95 : location_info := LocationInfo file_1 72 34 72 35.
  Definition loc_96 : location_info := LocationInfo file_1 72 34 72 35.
  Definition loc_97 : location_info := LocationInfo file_1 71 12 71 13.
  Definition loc_98 : location_info := LocationInfo file_1 71 16 71 24.
  Definition loc_99 : location_info := LocationInfo file_1 71 16 71 24.
  Definition loc_100 : location_info := LocationInfo file_1 71 16 71 17.
  Definition loc_101 : location_info := LocationInfo file_1 71 16 71 17.
  Definition loc_102 : location_info := LocationInfo file_1 68 12 68 40.
  Definition loc_103 : location_info := LocationInfo file_1 68 12 68 25.
  Definition loc_104 : location_info := LocationInfo file_1 68 12 68 25.
  Definition loc_105 : location_info := LocationInfo file_1 68 12 68 13.
  Definition loc_106 : location_info := LocationInfo file_1 68 12 68 13.
  Definition loc_107 : location_info := LocationInfo file_1 68 28 68 40.
  Definition loc_108 : location_info := LocationInfo file_1 68 28 68 40.
  Definition loc_109 : location_info := LocationInfo file_1 68 28 68 29.
  Definition loc_110 : location_info := LocationInfo file_1 68 28 68 29.
  Definition loc_111 : location_info := LocationInfo file_1 62 8 62 33.
  Definition loc_112 : location_info := LocationInfo file_1 62 8 62 15.
  Definition loc_113 : location_info := LocationInfo file_1 62 8 62 15.
  Definition loc_114 : location_info := LocationInfo file_1 62 8 62 9.
  Definition loc_115 : location_info := LocationInfo file_1 62 8 62 9.
  Definition loc_116 : location_info := LocationInfo file_1 62 19 62 33.
  Definition loc_119 : location_info := LocationInfo file_1 84 4 84 27.
  Definition loc_120 : location_info := LocationInfo file_1 86 4 86 22.
  Definition loc_121 : location_info := LocationInfo file_1 87 4 87 16.
  Definition loc_122 : location_info := LocationInfo file_1 87 4 87 11.
  Definition loc_123 : location_info := LocationInfo file_1 87 4 87 5.
  Definition loc_124 : location_info := LocationInfo file_1 87 4 87 5.
  Definition loc_125 : location_info := LocationInfo file_1 87 14 87 15.
  Definition loc_126 : location_info := LocationInfo file_1 87 14 87 15.
  Definition loc_127 : location_info := LocationInfo file_1 86 4 86 11.
  Definition loc_128 : location_info := LocationInfo file_1 86 4 86 5.
  Definition loc_129 : location_info := LocationInfo file_1 86 4 86 5.
  Definition loc_130 : location_info := LocationInfo file_1 86 14 86 21.
  Definition loc_131 : location_info := LocationInfo file_1 86 14 86 21.
  Definition loc_132 : location_info := LocationInfo file_1 86 14 86 15.
  Definition loc_133 : location_info := LocationInfo file_1 86 14 86 15.
  Definition loc_134 : location_info := LocationInfo file_1 84 25 84 26.
  Definition loc_135 : location_info := LocationInfo file_1 84 25 84 26.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [freelist]. *)
  Program Definition struct_freelist := {|
    sl_members := [
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [slab]. *)
  Program Definition struct_slab := {|
    sl_members := [
      (Some "chunksize", it_layout size_t);
      (Some "entry_size", it_layout size_t);
      (Some "chunk", void*);
      (Some "free", void*)
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

  (* Definition of function [slab_init]. *)
  Definition impl_slab_init : function := {|
    f_args := [
      ("s", void*);
      ("p", void*);
      ("chunksize", it_layout size_t);
      ("entry_size", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        LocInfoE loc_29 ((LocInfoE loc_30 (!{PtrOp} (LocInfoE loc_31 ("s")))) at{struct_slab} "chunk") <-{ PtrOp }
          LocInfoE loc_32 (use{PtrOp} (LocInfoE loc_33 ("p"))) ;
        locinfo: loc_12 ;
        LocInfoE loc_24 ((LocInfoE loc_25 (!{PtrOp} (LocInfoE loc_26 ("s")))) at{struct_slab} "chunksize") <-{ IntOp size_t }
          LocInfoE loc_27 (use{IntOp size_t} (LocInfoE loc_28 ("chunksize"))) ;
        locinfo: loc_13 ;
        LocInfoE loc_19 ((LocInfoE loc_20 (!{PtrOp} (LocInfoE loc_21 ("s")))) at{struct_slab} "entry_size") <-{ IntOp size_t }
          LocInfoE loc_22 (use{IntOp size_t} (LocInfoE loc_23 ("entry_size"))) ;
        locinfo: loc_14 ;
        LocInfoE loc_15 ((LocInfoE loc_16 (!{PtrOp} (LocInfoE loc_17 ("s")))) at{struct_slab} "free") <-{ PtrOp }
          LocInfoE loc_18 (NULL) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [slab_alloc]. *)
  Definition impl_slab_alloc : function := {|
    f_args := [
      ("s", void*)
    ];
    f_local_vars := [
      ("r", void*);
      ("f", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_111 ;
        if{IntOp i32, None}: LocInfoE loc_111 ((LocInfoE loc_112 (use{PtrOp} (LocInfoE loc_113 ((LocInfoE loc_114 (!{PtrOp} (LocInfoE loc_115 ("s")))) at{struct_slab} "free")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_116 (NULL)))
        then
        locinfo: loc_40 ;
          Goto "#1"
        else
        locinfo: loc_102 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_40 ;
        LocInfoE loc_56 ("f") <-{ PtrOp }
          LocInfoE loc_57 (use{PtrOp} (LocInfoE loc_58 ((LocInfoE loc_59 (!{PtrOp} (LocInfoE loc_60 ("s")))) at{struct_slab} "free"))) ;
        locinfo: loc_41 ;
        LocInfoE loc_49 ((LocInfoE loc_50 (!{PtrOp} (LocInfoE loc_51 ("s")))) at{struct_slab} "free") <-{ PtrOp }
          LocInfoE loc_52 (use{PtrOp} (LocInfoE loc_53 ((LocInfoE loc_54 (!{PtrOp} (LocInfoE loc_55 ("f")))) at{struct_freelist} "next"))) ;
        locinfo: loc_42 ;
        LocInfoE loc_46 ("r") <-{ PtrOp }
          LocInfoE loc_47 (use{PtrOp} (LocInfoE loc_48 ("f"))) ;
        locinfo: loc_43 ;
        Return (LocInfoE loc_44 (use{PtrOp} (LocInfoE loc_45 ("r"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_102 ;
        if{IntOp i32, None}: LocInfoE loc_102 ((LocInfoE loc_103 (use{IntOp size_t} (LocInfoE loc_104 ((LocInfoE loc_105 (!{PtrOp} (LocInfoE loc_106 ("s")))) at{struct_slab} "entry_size")))) >{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_107 (use{IntOp size_t} (LocInfoE loc_108 ((LocInfoE loc_109 (!{PtrOp} (LocInfoE loc_110 ("s")))) at{struct_slab} "chunksize")))))
        then
        locinfo: loc_64 ;
          Goto "#3"
        else
        locinfo: loc_67 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_64 ;
        Return (LocInfoE loc_65 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_67 ;
        LocInfoE loc_97 ("r") <-{ PtrOp }
          LocInfoE loc_98 (use{PtrOp} (LocInfoE loc_99 ((LocInfoE loc_100 (!{PtrOp} (LocInfoE loc_101 ("s")))) at{struct_slab} "chunk"))) ;
        locinfo: loc_68 ;
        LocInfoE loc_85 ((LocInfoE loc_86 (!{PtrOp} (LocInfoE loc_87 ("s")))) at{struct_slab} "chunk") <-{ PtrOp }
          LocInfoE loc_88 ((LocInfoE loc_89 (use{PtrOp} (LocInfoE loc_90 ((LocInfoE loc_91 (!{PtrOp} (LocInfoE loc_92 ("s")))) at{struct_slab} "chunk")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_93 (use{IntOp size_t} (LocInfoE loc_94 ((LocInfoE loc_95 (!{PtrOp} (LocInfoE loc_96 ("s")))) at{struct_slab} "entry_size"))))) ;
        locinfo: loc_69 ;
        LocInfoE loc_73 ((LocInfoE loc_74 (!{PtrOp} (LocInfoE loc_75 ("s")))) at{struct_slab} "chunksize") <-{ IntOp size_t }
          LocInfoE loc_76 ((LocInfoE loc_77 (use{IntOp size_t} (LocInfoE loc_78 ((LocInfoE loc_79 (!{PtrOp} (LocInfoE loc_80 ("s")))) at{struct_slab} "chunksize")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_81 (use{IntOp size_t} (LocInfoE loc_82 ((LocInfoE loc_83 (!{PtrOp} (LocInfoE loc_84 ("s")))) at{struct_slab} "entry_size"))))) ;
        locinfo: loc_70 ;
        Return (LocInfoE loc_71 (use{PtrOp} (LocInfoE loc_72 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [slab_free]. *)
  Definition impl_slab_free : function := {|
    f_args := [
      ("s", void*);
      ("x", void*)
    ];
    f_local_vars := [
      ("f", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "f" <-{ PtrOp }
          LocInfoE loc_134 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_134 (use{PtrOp} (LocInfoE loc_135 ("x"))))) ;
        locinfo: loc_120 ;
        LocInfoE loc_127 ((LocInfoE loc_128 (!{PtrOp} (LocInfoE loc_129 ("f")))) at{struct_freelist} "next") <-{ PtrOp }
          LocInfoE loc_130 (use{PtrOp} (LocInfoE loc_131 ((LocInfoE loc_132 (!{PtrOp} (LocInfoE loc_133 ("s")))) at{struct_slab} "free"))) ;
        locinfo: loc_121 ;
        LocInfoE loc_122 ((LocInfoE loc_123 (!{PtrOp} (LocInfoE loc_124 ("s")))) at{struct_slab} "free") <-{ PtrOp }
          LocInfoE loc_125 (use{PtrOp} (LocInfoE loc_126 ("f"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
