From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section code.
  Definition file_0 : string := "examples/malloc1.c".
  Definition loc_2 : location_info := LocationInfo file_0 45 4 45 17.
  Definition loc_3 : location_info := LocationInfo file_0 46 4 46 29.
  Definition loc_4 : location_info := LocationInfo file_0 47 4 47 31.
  Definition loc_5 : location_info := LocationInfo file_0 48 4 48 29.
  Definition loc_6 : location_info := LocationInfo file_0 48 4 48 11.
  Definition loc_7 : location_info := LocationInfo file_0 48 4 48 5.
  Definition loc_8 : location_info := LocationInfo file_0 48 4 48 5.
  Definition loc_9 : location_info := LocationInfo file_0 48 14 48 28.
  Definition loc_10 : location_info := LocationInfo file_0 47 4 47 17.
  Definition loc_11 : location_info := LocationInfo file_0 47 4 47 5.
  Definition loc_12 : location_info := LocationInfo file_0 47 4 47 5.
  Definition loc_13 : location_info := LocationInfo file_0 47 20 47 30.
  Definition loc_14 : location_info := LocationInfo file_0 47 20 47 30.
  Definition loc_15 : location_info := LocationInfo file_0 46 4 46 16.
  Definition loc_16 : location_info := LocationInfo file_0 46 4 46 5.
  Definition loc_17 : location_info := LocationInfo file_0 46 4 46 5.
  Definition loc_18 : location_info := LocationInfo file_0 46 19 46 28.
  Definition loc_19 : location_info := LocationInfo file_0 46 19 46 28.
  Definition loc_20 : location_info := LocationInfo file_0 45 4 45 12.
  Definition loc_21 : location_info := LocationInfo file_0 45 4 45 5.
  Definition loc_22 : location_info := LocationInfo file_0 45 4 45 5.
  Definition loc_23 : location_info := LocationInfo file_0 45 15 45 16.
  Definition loc_24 : location_info := LocationInfo file_0 45 15 45 16.
  Definition loc_27 : location_info := LocationInfo file_0 59 4 73 5.
  Definition loc_28 : location_info := LocationInfo file_0 59 35 64 5.
  Definition loc_29 : location_info := LocationInfo file_0 60 8 60 20.
  Definition loc_30 : location_info := LocationInfo file_0 61 8 61 26.
  Definition loc_31 : location_info := LocationInfo file_0 62 8 62 14.
  Definition loc_32 : location_info := LocationInfo file_0 63 8 63 17.
  Definition loc_33 : location_info := LocationInfo file_0 63 15 63 16.
  Definition loc_34 : location_info := LocationInfo file_0 63 15 63 16.
  Definition loc_35 : location_info := LocationInfo file_0 62 8 62 9.
  Definition loc_36 : location_info := LocationInfo file_0 62 12 62 13.
  Definition loc_37 : location_info := LocationInfo file_0 62 12 62 13.
  Definition loc_38 : location_info := LocationInfo file_0 61 8 61 15.
  Definition loc_39 : location_info := LocationInfo file_0 61 8 61 9.
  Definition loc_40 : location_info := LocationInfo file_0 61 8 61 9.
  Definition loc_41 : location_info := LocationInfo file_0 61 18 61 25.
  Definition loc_42 : location_info := LocationInfo file_0 61 18 61 25.
  Definition loc_43 : location_info := LocationInfo file_0 61 18 61 19.
  Definition loc_44 : location_info := LocationInfo file_0 61 18 61 19.
  Definition loc_45 : location_info := LocationInfo file_0 60 8 60 9.
  Definition loc_46 : location_info := LocationInfo file_0 60 12 60 19.
  Definition loc_47 : location_info := LocationInfo file_0 60 12 60 19.
  Definition loc_48 : location_info := LocationInfo file_0 60 12 60 13.
  Definition loc_49 : location_info := LocationInfo file_0 60 12 60 13.
  Definition loc_50 : location_info := LocationInfo file_0 64 11 73 5.
  Definition loc_51 : location_info := LocationInfo file_0 65 8 72 9.
  Definition loc_52 : location_info := LocationInfo file_0 65 42 67 9.
  Definition loc_53 : location_info := LocationInfo file_0 66 12 66 34.
  Definition loc_54 : location_info := LocationInfo file_0 66 19 66 33.
  Definition loc_55 : location_info := LocationInfo file_0 67 15 72 9.
  Definition loc_56 : location_info := LocationInfo file_0 68 12 68 25.
  Definition loc_57 : location_info := LocationInfo file_0 69 12 69 48.
  Definition loc_58 : location_info := LocationInfo file_0 70 12 70 56.
  Definition loc_59 : location_info := LocationInfo file_0 71 12 71 21.
  Definition loc_60 : location_info := LocationInfo file_0 71 19 71 20.
  Definition loc_61 : location_info := LocationInfo file_0 71 19 71 20.
  Definition loc_62 : location_info := LocationInfo file_0 70 12 70 24.
  Definition loc_63 : location_info := LocationInfo file_0 70 12 70 13.
  Definition loc_64 : location_info := LocationInfo file_0 70 12 70 13.
  Definition loc_65 : location_info := LocationInfo file_0 70 27 70 55.
  Definition loc_66 : location_info := LocationInfo file_0 70 27 70 39.
  Definition loc_67 : location_info := LocationInfo file_0 70 27 70 39.
  Definition loc_68 : location_info := LocationInfo file_0 70 27 70 28.
  Definition loc_69 : location_info := LocationInfo file_0 70 27 70 28.
  Definition loc_70 : location_info := LocationInfo file_0 70 42 70 55.
  Definition loc_71 : location_info := LocationInfo file_0 70 42 70 55.
  Definition loc_72 : location_info := LocationInfo file_0 70 42 70 43.
  Definition loc_73 : location_info := LocationInfo file_0 70 42 70 43.
  Definition loc_74 : location_info := LocationInfo file_0 69 12 69 20.
  Definition loc_75 : location_info := LocationInfo file_0 69 12 69 13.
  Definition loc_76 : location_info := LocationInfo file_0 69 12 69 13.
  Definition loc_77 : location_info := LocationInfo file_0 69 23 69 47.
  Definition loc_78 : location_info := LocationInfo file_0 69 23 69 31.
  Definition loc_79 : location_info := LocationInfo file_0 69 23 69 31.
  Definition loc_80 : location_info := LocationInfo file_0 69 23 69 24.
  Definition loc_81 : location_info := LocationInfo file_0 69 23 69 24.
  Definition loc_82 : location_info := LocationInfo file_0 69 34 69 47.
  Definition loc_83 : location_info := LocationInfo file_0 69 34 69 47.
  Definition loc_84 : location_info := LocationInfo file_0 69 34 69 35.
  Definition loc_85 : location_info := LocationInfo file_0 69 34 69 35.
  Definition loc_86 : location_info := LocationInfo file_0 68 12 68 13.
  Definition loc_87 : location_info := LocationInfo file_0 68 16 68 24.
  Definition loc_88 : location_info := LocationInfo file_0 68 16 68 24.
  Definition loc_89 : location_info := LocationInfo file_0 68 16 68 17.
  Definition loc_90 : location_info := LocationInfo file_0 68 16 68 17.
  Definition loc_91 : location_info := LocationInfo file_0 65 12 65 40.
  Definition loc_92 : location_info := LocationInfo file_0 65 12 65 25.
  Definition loc_93 : location_info := LocationInfo file_0 65 12 65 25.
  Definition loc_94 : location_info := LocationInfo file_0 65 12 65 13.
  Definition loc_95 : location_info := LocationInfo file_0 65 12 65 13.
  Definition loc_96 : location_info := LocationInfo file_0 65 28 65 40.
  Definition loc_97 : location_info := LocationInfo file_0 65 28 65 40.
  Definition loc_98 : location_info := LocationInfo file_0 65 28 65 29.
  Definition loc_99 : location_info := LocationInfo file_0 65 28 65 29.
  Definition loc_100 : location_info := LocationInfo file_0 59 8 59 33.
  Definition loc_101 : location_info := LocationInfo file_0 59 8 59 15.
  Definition loc_102 : location_info := LocationInfo file_0 59 8 59 15.
  Definition loc_103 : location_info := LocationInfo file_0 59 8 59 9.
  Definition loc_104 : location_info := LocationInfo file_0 59 8 59 9.
  Definition loc_105 : location_info := LocationInfo file_0 59 19 59 33.
  Definition loc_108 : location_info := LocationInfo file_0 81 4 81 27.
  Definition loc_109 : location_info := LocationInfo file_0 83 4 83 10.
  Definition loc_110 : location_info := LocationInfo file_0 83 10 83 5.
  Definition loc_111 : location_info := LocationInfo file_0 85 4 85 22.
  Definition loc_112 : location_info := LocationInfo file_0 86 4 86 16.
  Definition loc_113 : location_info := LocationInfo file_0 86 4 86 11.
  Definition loc_114 : location_info := LocationInfo file_0 86 4 86 5.
  Definition loc_115 : location_info := LocationInfo file_0 86 4 86 5.
  Definition loc_116 : location_info := LocationInfo file_0 86 14 86 15.
  Definition loc_117 : location_info := LocationInfo file_0 86 14 86 15.
  Definition loc_118 : location_info := LocationInfo file_0 85 4 85 11.
  Definition loc_119 : location_info := LocationInfo file_0 85 4 85 5.
  Definition loc_120 : location_info := LocationInfo file_0 85 4 85 5.
  Definition loc_121 : location_info := LocationInfo file_0 85 14 85 21.
  Definition loc_122 : location_info := LocationInfo file_0 85 14 85 21.
  Definition loc_123 : location_info := LocationInfo file_0 85 14 85 15.
  Definition loc_124 : location_info := LocationInfo file_0 85 14 85 15.
  Definition loc_125 : location_info := LocationInfo file_0 83 4 83 9.
  Definition loc_126 : location_info := LocationInfo file_0 83 5 83 9.
  Definition loc_127 : location_info := LocationInfo file_0 83 7 83 8.
  Definition loc_128 : location_info := LocationInfo file_0 83 7 83 8.
  Definition loc_129 : location_info := LocationInfo file_0 81 25 81 26.
  Definition loc_130 : location_info := LocationInfo file_0 81 25 81 26.

  (* Definition of struct [freelist]. *)
  Program Definition struct_freelist := {|
    sl_members := [
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [slab]. *)
  Program Definition struct_slab := {|
    sl_members := [
      (Some "chunksize", it_layout size_t);
      (Some "entry_size", it_layout size_t);
      (Some "chunk", LPtr);
      (Some "free", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [slab_init]. *)
  Definition impl_slab_init : function := {|
    f_args := [
      ("s", LPtr);
      ("p", LPtr);
      ("chunksize", it_layout size_t);
      ("entry_size", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_20 ((LocInfoE loc_21 (!{LPtr} (LocInfoE loc_22 ("s")))) at{struct_slab} "chunk") <-{ LPtr }
          LocInfoE loc_23 (use{LPtr} (LocInfoE loc_24 ("p"))) ;
        locinfo: loc_3 ;
        LocInfoE loc_15 ((LocInfoE loc_16 (!{LPtr} (LocInfoE loc_17 ("s")))) at{struct_slab} "chunksize") <-{ it_layout size_t }
          LocInfoE loc_18 (use{it_layout size_t} (LocInfoE loc_19 ("chunksize"))) ;
        locinfo: loc_4 ;
        LocInfoE loc_10 ((LocInfoE loc_11 (!{LPtr} (LocInfoE loc_12 ("s")))) at{struct_slab} "entry_size") <-{ it_layout size_t }
          LocInfoE loc_13 (use{it_layout size_t} (LocInfoE loc_14 ("entry_size"))) ;
        locinfo: loc_5 ;
        LocInfoE loc_6 ((LocInfoE loc_7 (!{LPtr} (LocInfoE loc_8 ("s")))) at{struct_slab} "free") <-{ LPtr }
          LocInfoE loc_9 (NULL) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [slab_alloc]. *)
  Definition impl_slab_alloc : function := {|
    f_args := [
      ("s", LPtr)
    ];
    f_local_vars := [
      ("r", LPtr);
      ("f", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_100 ;
        if: LocInfoE loc_100 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_100 ((LocInfoE loc_101 (use{LPtr} (LocInfoE loc_102 ((LocInfoE loc_103 (!{LPtr} (LocInfoE loc_104 ("s")))) at{struct_slab} "free")))) !={PtrOp, PtrOp} (LocInfoE loc_105 (NULL)))))
        then
        locinfo: loc_29 ;
          Goto "#1"
        else
        locinfo: loc_91 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_29 ;
        LocInfoE loc_45 ("f") <-{ LPtr }
          LocInfoE loc_46 (use{LPtr} (LocInfoE loc_47 ((LocInfoE loc_48 (!{LPtr} (LocInfoE loc_49 ("s")))) at{struct_slab} "free"))) ;
        locinfo: loc_30 ;
        LocInfoE loc_38 ((LocInfoE loc_39 (!{LPtr} (LocInfoE loc_40 ("s")))) at{struct_slab} "free") <-{ LPtr }
          LocInfoE loc_41 (use{LPtr} (LocInfoE loc_42 ((LocInfoE loc_43 (!{LPtr} (LocInfoE loc_44 ("f")))) at{struct_freelist} "next"))) ;
        locinfo: loc_31 ;
        LocInfoE loc_35 ("r") <-{ LPtr }
          LocInfoE loc_36 (use{LPtr} (LocInfoE loc_37 ("f"))) ;
        locinfo: loc_32 ;
        Return (LocInfoE loc_33 (use{LPtr} (LocInfoE loc_34 ("r"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_91 ;
        if: LocInfoE loc_91 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_91 ((LocInfoE loc_92 (use{it_layout size_t} (LocInfoE loc_93 ((LocInfoE loc_94 (!{LPtr} (LocInfoE loc_95 ("s")))) at{struct_slab} "entry_size")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_96 (use{it_layout size_t} (LocInfoE loc_97 ((LocInfoE loc_98 (!{LPtr} (LocInfoE loc_99 ("s")))) at{struct_slab} "chunksize")))))))
        then
        locinfo: loc_53 ;
          Goto "#3"
        else
        locinfo: loc_56 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_53 ;
        Return (LocInfoE loc_54 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_56 ;
        LocInfoE loc_86 ("r") <-{ LPtr }
          LocInfoE loc_87 (use{LPtr} (LocInfoE loc_88 ((LocInfoE loc_89 (!{LPtr} (LocInfoE loc_90 ("s")))) at{struct_slab} "chunk"))) ;
        locinfo: loc_57 ;
        LocInfoE loc_74 ((LocInfoE loc_75 (!{LPtr} (LocInfoE loc_76 ("s")))) at{struct_slab} "chunk") <-{ LPtr }
          LocInfoE loc_77 ((LocInfoE loc_78 (use{LPtr} (LocInfoE loc_79 ((LocInfoE loc_80 (!{LPtr} (LocInfoE loc_81 ("s")))) at{struct_slab} "chunk")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_82 (use{it_layout size_t} (LocInfoE loc_83 ((LocInfoE loc_84 (!{LPtr} (LocInfoE loc_85 ("s")))) at{struct_slab} "entry_size"))))) ;
        locinfo: loc_58 ;
        LocInfoE loc_62 ((LocInfoE loc_63 (!{LPtr} (LocInfoE loc_64 ("s")))) at{struct_slab} "chunksize") <-{ it_layout size_t }
          LocInfoE loc_65 ((LocInfoE loc_66 (use{it_layout size_t} (LocInfoE loc_67 ((LocInfoE loc_68 (!{LPtr} (LocInfoE loc_69 ("s")))) at{struct_slab} "chunksize")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_70 (use{it_layout size_t} (LocInfoE loc_71 ((LocInfoE loc_72 (!{LPtr} (LocInfoE loc_73 ("s")))) at{struct_slab} "entry_size"))))) ;
        locinfo: loc_59 ;
        Return (LocInfoE loc_60 (use{LPtr} (LocInfoE loc_61 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [slab_free]. *)
  Definition impl_slab_free : function := {|
    f_args := [
      ("s", LPtr);
      ("x", LPtr)
    ];
    f_local_vars := [
      ("f", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "f" <-{ LPtr }
          LocInfoE loc_129 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_129 (use{LPtr} (LocInfoE loc_130 ("x"))))) ;
        locinfo: loc_109 ;
        expr: (LocInfoE loc_125 (&(LocInfoE loc_127 (!{LPtr} (LocInfoE loc_128 ("s")))))) ;
        locinfo: loc_111 ;
        LocInfoE loc_118 ((LocInfoE loc_119 (!{LPtr} (LocInfoE loc_120 ("f")))) at{struct_freelist} "next") <-{ LPtr }
          LocInfoE loc_121 (use{LPtr} (LocInfoE loc_122 ((LocInfoE loc_123 (!{LPtr} (LocInfoE loc_124 ("s")))) at{struct_slab} "free"))) ;
        locinfo: loc_112 ;
        LocInfoE loc_113 ((LocInfoE loc_114 (!{LPtr} (LocInfoE loc_115 ("s")))) at{struct_slab} "free") <-{ LPtr }
          LocInfoE loc_116 (use{LPtr} (LocInfoE loc_117 ("f"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
