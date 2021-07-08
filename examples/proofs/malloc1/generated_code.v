From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/malloc1.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 45 4 45 17.
  Definition loc_12 : location_info := LocationInfo file_1 46 4 46 29.
  Definition loc_13 : location_info := LocationInfo file_1 47 4 47 31.
  Definition loc_14 : location_info := LocationInfo file_1 48 4 48 29.
  Definition loc_15 : location_info := LocationInfo file_1 48 4 48 11.
  Definition loc_16 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_17 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_18 : location_info := LocationInfo file_1 48 14 48 28.
  Definition loc_19 : location_info := LocationInfo file_1 47 4 47 17.
  Definition loc_20 : location_info := LocationInfo file_1 47 4 47 5.
  Definition loc_21 : location_info := LocationInfo file_1 47 4 47 5.
  Definition loc_22 : location_info := LocationInfo file_1 47 20 47 30.
  Definition loc_23 : location_info := LocationInfo file_1 47 20 47 30.
  Definition loc_24 : location_info := LocationInfo file_1 46 4 46 16.
  Definition loc_25 : location_info := LocationInfo file_1 46 4 46 5.
  Definition loc_26 : location_info := LocationInfo file_1 46 4 46 5.
  Definition loc_27 : location_info := LocationInfo file_1 46 19 46 28.
  Definition loc_28 : location_info := LocationInfo file_1 46 19 46 28.
  Definition loc_29 : location_info := LocationInfo file_1 45 4 45 12.
  Definition loc_30 : location_info := LocationInfo file_1 45 4 45 5.
  Definition loc_31 : location_info := LocationInfo file_1 45 4 45 5.
  Definition loc_32 : location_info := LocationInfo file_1 45 15 45 16.
  Definition loc_33 : location_info := LocationInfo file_1 45 15 45 16.
  Definition loc_36 : location_info := LocationInfo file_1 60 4 74 5.
  Definition loc_37 : location_info := LocationInfo file_1 60 35 65 5.
  Definition loc_38 : location_info := LocationInfo file_1 61 8 61 20.
  Definition loc_39 : location_info := LocationInfo file_1 62 8 62 26.
  Definition loc_40 : location_info := LocationInfo file_1 63 8 63 14.
  Definition loc_41 : location_info := LocationInfo file_1 64 8 64 17.
  Definition loc_42 : location_info := LocationInfo file_1 64 15 64 16.
  Definition loc_43 : location_info := LocationInfo file_1 64 15 64 16.
  Definition loc_44 : location_info := LocationInfo file_1 63 8 63 9.
  Definition loc_45 : location_info := LocationInfo file_1 63 12 63 13.
  Definition loc_46 : location_info := LocationInfo file_1 63 12 63 13.
  Definition loc_47 : location_info := LocationInfo file_1 62 8 62 15.
  Definition loc_48 : location_info := LocationInfo file_1 62 8 62 9.
  Definition loc_49 : location_info := LocationInfo file_1 62 8 62 9.
  Definition loc_50 : location_info := LocationInfo file_1 62 18 62 25.
  Definition loc_51 : location_info := LocationInfo file_1 62 18 62 25.
  Definition loc_52 : location_info := LocationInfo file_1 62 18 62 19.
  Definition loc_53 : location_info := LocationInfo file_1 62 18 62 19.
  Definition loc_54 : location_info := LocationInfo file_1 61 8 61 9.
  Definition loc_55 : location_info := LocationInfo file_1 61 12 61 19.
  Definition loc_56 : location_info := LocationInfo file_1 61 12 61 19.
  Definition loc_57 : location_info := LocationInfo file_1 61 12 61 13.
  Definition loc_58 : location_info := LocationInfo file_1 61 12 61 13.
  Definition loc_59 : location_info := LocationInfo file_1 65 11 74 5.
  Definition loc_60 : location_info := LocationInfo file_1 66 8 73 9.
  Definition loc_61 : location_info := LocationInfo file_1 66 42 68 9.
  Definition loc_62 : location_info := LocationInfo file_1 67 12 67 34.
  Definition loc_63 : location_info := LocationInfo file_1 67 19 67 33.
  Definition loc_64 : location_info := LocationInfo file_1 68 15 73 9.
  Definition loc_65 : location_info := LocationInfo file_1 69 12 69 25.
  Definition loc_66 : location_info := LocationInfo file_1 70 12 70 48.
  Definition loc_67 : location_info := LocationInfo file_1 71 12 71 56.
  Definition loc_68 : location_info := LocationInfo file_1 72 12 72 21.
  Definition loc_69 : location_info := LocationInfo file_1 72 19 72 20.
  Definition loc_70 : location_info := LocationInfo file_1 72 19 72 20.
  Definition loc_71 : location_info := LocationInfo file_1 71 12 71 24.
  Definition loc_72 : location_info := LocationInfo file_1 71 12 71 13.
  Definition loc_73 : location_info := LocationInfo file_1 71 12 71 13.
  Definition loc_74 : location_info := LocationInfo file_1 71 27 71 55.
  Definition loc_75 : location_info := LocationInfo file_1 71 27 71 39.
  Definition loc_76 : location_info := LocationInfo file_1 71 27 71 39.
  Definition loc_77 : location_info := LocationInfo file_1 71 27 71 28.
  Definition loc_78 : location_info := LocationInfo file_1 71 27 71 28.
  Definition loc_79 : location_info := LocationInfo file_1 71 42 71 55.
  Definition loc_80 : location_info := LocationInfo file_1 71 42 71 55.
  Definition loc_81 : location_info := LocationInfo file_1 71 42 71 43.
  Definition loc_82 : location_info := LocationInfo file_1 71 42 71 43.
  Definition loc_83 : location_info := LocationInfo file_1 70 12 70 20.
  Definition loc_84 : location_info := LocationInfo file_1 70 12 70 13.
  Definition loc_85 : location_info := LocationInfo file_1 70 12 70 13.
  Definition loc_86 : location_info := LocationInfo file_1 70 23 70 47.
  Definition loc_87 : location_info := LocationInfo file_1 70 23 70 31.
  Definition loc_88 : location_info := LocationInfo file_1 70 23 70 31.
  Definition loc_89 : location_info := LocationInfo file_1 70 23 70 24.
  Definition loc_90 : location_info := LocationInfo file_1 70 23 70 24.
  Definition loc_91 : location_info := LocationInfo file_1 70 34 70 47.
  Definition loc_92 : location_info := LocationInfo file_1 70 34 70 47.
  Definition loc_93 : location_info := LocationInfo file_1 70 34 70 35.
  Definition loc_94 : location_info := LocationInfo file_1 70 34 70 35.
  Definition loc_95 : location_info := LocationInfo file_1 69 12 69 13.
  Definition loc_96 : location_info := LocationInfo file_1 69 16 69 24.
  Definition loc_97 : location_info := LocationInfo file_1 69 16 69 24.
  Definition loc_98 : location_info := LocationInfo file_1 69 16 69 17.
  Definition loc_99 : location_info := LocationInfo file_1 69 16 69 17.
  Definition loc_100 : location_info := LocationInfo file_1 66 12 66 40.
  Definition loc_101 : location_info := LocationInfo file_1 66 12 66 25.
  Definition loc_102 : location_info := LocationInfo file_1 66 12 66 25.
  Definition loc_103 : location_info := LocationInfo file_1 66 12 66 13.
  Definition loc_104 : location_info := LocationInfo file_1 66 12 66 13.
  Definition loc_105 : location_info := LocationInfo file_1 66 28 66 40.
  Definition loc_106 : location_info := LocationInfo file_1 66 28 66 40.
  Definition loc_107 : location_info := LocationInfo file_1 66 28 66 29.
  Definition loc_108 : location_info := LocationInfo file_1 66 28 66 29.
  Definition loc_109 : location_info := LocationInfo file_1 60 8 60 33.
  Definition loc_110 : location_info := LocationInfo file_1 60 8 60 15.
  Definition loc_111 : location_info := LocationInfo file_1 60 8 60 15.
  Definition loc_112 : location_info := LocationInfo file_1 60 8 60 9.
  Definition loc_113 : location_info := LocationInfo file_1 60 8 60 9.
  Definition loc_114 : location_info := LocationInfo file_1 60 19 60 33.
  Definition loc_117 : location_info := LocationInfo file_1 82 4 82 27.
  Definition loc_118 : location_info := LocationInfo file_1 84 4 84 22.
  Definition loc_119 : location_info := LocationInfo file_1 85 4 85 16.
  Definition loc_120 : location_info := LocationInfo file_1 85 4 85 11.
  Definition loc_121 : location_info := LocationInfo file_1 85 4 85 5.
  Definition loc_122 : location_info := LocationInfo file_1 85 4 85 5.
  Definition loc_123 : location_info := LocationInfo file_1 85 14 85 15.
  Definition loc_124 : location_info := LocationInfo file_1 85 14 85 15.
  Definition loc_125 : location_info := LocationInfo file_1 84 4 84 11.
  Definition loc_126 : location_info := LocationInfo file_1 84 4 84 5.
  Definition loc_127 : location_info := LocationInfo file_1 84 4 84 5.
  Definition loc_128 : location_info := LocationInfo file_1 84 14 84 21.
  Definition loc_129 : location_info := LocationInfo file_1 84 14 84 21.
  Definition loc_130 : location_info := LocationInfo file_1 84 14 84 15.
  Definition loc_131 : location_info := LocationInfo file_1 84 14 84 15.
  Definition loc_132 : location_info := LocationInfo file_1 82 25 82 26.
  Definition loc_133 : location_info := LocationInfo file_1 82 25 82 26.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
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
        LocInfoE loc_29 ((LocInfoE loc_30 (!{void*} (LocInfoE loc_31 ("s")))) at{struct_slab} "chunk") <-{ void* }
          LocInfoE loc_32 (use{void*} (LocInfoE loc_33 ("p"))) ;
        locinfo: loc_12 ;
        LocInfoE loc_24 ((LocInfoE loc_25 (!{void*} (LocInfoE loc_26 ("s")))) at{struct_slab} "chunksize") <-{ it_layout size_t }
          LocInfoE loc_27 (use{it_layout size_t} (LocInfoE loc_28 ("chunksize"))) ;
        locinfo: loc_13 ;
        LocInfoE loc_19 ((LocInfoE loc_20 (!{void*} (LocInfoE loc_21 ("s")))) at{struct_slab} "entry_size") <-{ it_layout size_t }
          LocInfoE loc_22 (use{it_layout size_t} (LocInfoE loc_23 ("entry_size"))) ;
        locinfo: loc_14 ;
        LocInfoE loc_15 ((LocInfoE loc_16 (!{void*} (LocInfoE loc_17 ("s")))) at{struct_slab} "free") <-{ void* }
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
        locinfo: loc_109 ;
        if: LocInfoE loc_109 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_109 ((LocInfoE loc_110 (use{void*} (LocInfoE loc_111 ((LocInfoE loc_112 (!{void*} (LocInfoE loc_113 ("s")))) at{struct_slab} "free")))) !={PtrOp, PtrOp} (LocInfoE loc_114 (NULL)))))
        then
        locinfo: loc_38 ;
          Goto "#1"
        else
        locinfo: loc_100 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_38 ;
        LocInfoE loc_54 ("f") <-{ void* }
          LocInfoE loc_55 (use{void*} (LocInfoE loc_56 ((LocInfoE loc_57 (!{void*} (LocInfoE loc_58 ("s")))) at{struct_slab} "free"))) ;
        locinfo: loc_39 ;
        LocInfoE loc_47 ((LocInfoE loc_48 (!{void*} (LocInfoE loc_49 ("s")))) at{struct_slab} "free") <-{ void* }
          LocInfoE loc_50 (use{void*} (LocInfoE loc_51 ((LocInfoE loc_52 (!{void*} (LocInfoE loc_53 ("f")))) at{struct_freelist} "next"))) ;
        locinfo: loc_40 ;
        LocInfoE loc_44 ("r") <-{ void* }
          LocInfoE loc_45 (use{void*} (LocInfoE loc_46 ("f"))) ;
        locinfo: loc_41 ;
        Return (LocInfoE loc_42 (use{void*} (LocInfoE loc_43 ("r"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_100 ;
        if: LocInfoE loc_100 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_100 ((LocInfoE loc_101 (use{it_layout size_t} (LocInfoE loc_102 ((LocInfoE loc_103 (!{void*} (LocInfoE loc_104 ("s")))) at{struct_slab} "entry_size")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_105 (use{it_layout size_t} (LocInfoE loc_106 ((LocInfoE loc_107 (!{void*} (LocInfoE loc_108 ("s")))) at{struct_slab} "chunksize")))))))
        then
        locinfo: loc_62 ;
          Goto "#3"
        else
        locinfo: loc_65 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_62 ;
        Return (LocInfoE loc_63 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_65 ;
        LocInfoE loc_95 ("r") <-{ void* }
          LocInfoE loc_96 (use{void*} (LocInfoE loc_97 ((LocInfoE loc_98 (!{void*} (LocInfoE loc_99 ("s")))) at{struct_slab} "chunk"))) ;
        locinfo: loc_66 ;
        LocInfoE loc_83 ((LocInfoE loc_84 (!{void*} (LocInfoE loc_85 ("s")))) at{struct_slab} "chunk") <-{ void* }
          LocInfoE loc_86 ((LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ((LocInfoE loc_89 (!{void*} (LocInfoE loc_90 ("s")))) at{struct_slab} "chunk")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_91 (use{it_layout size_t} (LocInfoE loc_92 ((LocInfoE loc_93 (!{void*} (LocInfoE loc_94 ("s")))) at{struct_slab} "entry_size"))))) ;
        locinfo: loc_67 ;
        LocInfoE loc_71 ((LocInfoE loc_72 (!{void*} (LocInfoE loc_73 ("s")))) at{struct_slab} "chunksize") <-{ it_layout size_t }
          LocInfoE loc_74 ((LocInfoE loc_75 (use{it_layout size_t} (LocInfoE loc_76 ((LocInfoE loc_77 (!{void*} (LocInfoE loc_78 ("s")))) at{struct_slab} "chunksize")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_79 (use{it_layout size_t} (LocInfoE loc_80 ((LocInfoE loc_81 (!{void*} (LocInfoE loc_82 ("s")))) at{struct_slab} "entry_size"))))) ;
        locinfo: loc_68 ;
        Return (LocInfoE loc_69 (use{void*} (LocInfoE loc_70 ("r"))))
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
        "f" <-{ void* }
          LocInfoE loc_132 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_132 (use{void*} (LocInfoE loc_133 ("x"))))) ;
        locinfo: loc_118 ;
        LocInfoE loc_125 ((LocInfoE loc_126 (!{void*} (LocInfoE loc_127 ("f")))) at{struct_freelist} "next") <-{ void* }
          LocInfoE loc_128 (use{void*} (LocInfoE loc_129 ((LocInfoE loc_130 (!{void*} (LocInfoE loc_131 ("s")))) at{struct_slab} "free"))) ;
        locinfo: loc_119 ;
        LocInfoE loc_120 ((LocInfoE loc_121 (!{void*} (LocInfoE loc_122 ("s")))) at{struct_slab} "free") <-{ void* }
          LocInfoE loc_123 (use{void*} (LocInfoE loc_124 ("f"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
