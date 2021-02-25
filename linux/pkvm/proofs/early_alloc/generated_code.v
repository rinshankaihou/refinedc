From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/pkvm/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 42 2 42 52.
  Definition loc_3 : location_info := LocationInfo file_0 42 9 42 51.
  Definition loc_4 : location_info := LocationInfo file_0 42 9 42 45.
  Definition loc_5 : location_info := LocationInfo file_0 42 10 42 19.
  Definition loc_6 : location_info := LocationInfo file_0 42 10 42 19.
  Definition loc_7 : location_info := LocationInfo file_0 42 11 42 14.
  Definition loc_8 : location_info := LocationInfo file_0 42 22 42 44.
  Definition loc_9 : location_info := LocationInfo file_0 42 34 42 44.
  Definition loc_10 : location_info := LocationInfo file_0 42 34 42 44.
  Definition loc_11 : location_info := LocationInfo file_0 42 35 42 38.
  Definition loc_12 : location_info := LocationInfo file_0 42 49 42 51.
  Definition loc_15 : location_info := LocationInfo file_0 59 2 59 31.
  Definition loc_16 : location_info := LocationInfo file_0 62 2 63 26.
  Definition loc_17 : location_info := LocationInfo file_0 65 2 65 16.
  Definition loc_18 : location_info := LocationInfo file_0 65 16 65 3.
  Definition loc_19 : location_info := LocationInfo file_0 66 2 66 30.
  Definition loc_20 : location_info := LocationInfo file_0 67 2 70 3.
  Definition loc_21 : location_info := LocationInfo file_0 80 2 84 3.
  Definition loc_22 : location_info := LocationInfo file_0 80 7 80 12.
  Definition loc_23 : location_info := LocationInfo file_0 80 2 84 3.
  Definition loc_24 : location_info := LocationInfo file_0 86 2 86 67.
  Definition loc_25 : location_info := LocationInfo file_0 86 9 86 66.
  Definition loc_26 : location_info := LocationInfo file_0 86 35 86 47.
  Definition loc_27 : location_info := LocationInfo file_0 86 35 86 47.
  Definition loc_28 : location_info := LocationInfo file_0 86 37 86 40.
  Definition loc_29 : location_info := LocationInfo file_0 86 51 86 65.
  Definition loc_30 : location_info := LocationInfo file_0 86 61 86 64.
  Definition loc_31 : location_info := LocationInfo file_0 86 61 86 64.
  Definition loc_32 : location_info := LocationInfo file_0 80 33 84 3.
  Definition loc_33 : location_info := LocationInfo file_0 81 4 81 18.
  Definition loc_34 : location_info := LocationInfo file_0 81 18 81 5.
  Definition loc_35 : location_info := LocationInfo file_0 82 4 82 24.
  Definition loc_36 : location_info := LocationInfo file_0 83 4 83 73.
  Definition loc_37 : location_info := LocationInfo file_0 80 2 84 3.
  Definition loc_38 : location_info := LocationInfo file_0 80 28 80 31.
  Definition loc_39 : location_info := LocationInfo file_0 80 28 80 29.
  Definition loc_40 : location_info := LocationInfo file_0 83 4 83 14.
  Definition loc_41 : location_info := LocationInfo file_0 83 4 83 14.
  Definition loc_42 : location_info := LocationInfo file_0 83 15 83 71.
  Definition loc_43 : location_info := LocationInfo file_0 83 41 83 53.
  Definition loc_44 : location_info := LocationInfo file_0 83 41 83 53.
  Definition loc_45 : location_info := LocationInfo file_0 83 43 83 46.
  Definition loc_46 : location_info := LocationInfo file_0 83 57 83 70.
  Definition loc_47 : location_info := LocationInfo file_0 83 66 83 69.
  Definition loc_48 : location_info := LocationInfo file_0 83 66 83 69.
  Definition loc_49 : location_info := LocationInfo file_0 82 4 82 5.
  Definition loc_50 : location_info := LocationInfo file_0 82 8 82 23.
  Definition loc_51 : location_info := LocationInfo file_0 82 8 82 11.
  Definition loc_52 : location_info := LocationInfo file_0 82 8 82 11.
  Definition loc_53 : location_info := LocationInfo file_0 82 14 82 23.
  Definition loc_54 : location_info := LocationInfo file_0 82 15 82 16.
  Definition loc_55 : location_info := LocationInfo file_0 82 15 82 16.
  Definition loc_56 : location_info := LocationInfo file_0 82 20 82 22.
  Definition loc_57 : location_info := LocationInfo file_0 81 4 81 17.
  Definition loc_58 : location_info := LocationInfo file_0 81 5 81 17.
  Definition loc_59 : location_info := LocationInfo file_0 81 7 81 10.
  Definition loc_60 : location_info := LocationInfo file_0 80 14 80 26.
  Definition loc_61 : location_info := LocationInfo file_0 80 14 80 15.
  Definition loc_62 : location_info := LocationInfo file_0 80 14 80 15.
  Definition loc_63 : location_info := LocationInfo file_0 80 18 80 26.
  Definition loc_64 : location_info := LocationInfo file_0 80 18 80 26.
  Definition loc_65 : location_info := LocationInfo file_0 80 7 80 8.
  Definition loc_66 : location_info := LocationInfo file_0 80 11 80 12.
  Definition loc_67 : location_info := LocationInfo file_0 67 29 70 3.
  Definition loc_68 : location_info := LocationInfo file_0 68 4 68 20.
  Definition loc_69 : location_info := LocationInfo file_0 69 4 69 26.
  Definition loc_70 : location_info := LocationInfo file_0 69 11 69 25.
  Definition loc_71 : location_info := LocationInfo file_0 68 4 68 13.
  Definition loc_72 : location_info := LocationInfo file_0 68 5 68 8.
  Definition loc_73 : location_info := LocationInfo file_0 68 16 68 19.
  Definition loc_74 : location_info := LocationInfo file_0 68 16 68 19.
  Definition loc_76 : location_info := LocationInfo file_0 67 6 67 27.
  Definition loc_77 : location_info := LocationInfo file_0 67 6 67 15.
  Definition loc_78 : location_info := LocationInfo file_0 67 6 67 15.
  Definition loc_79 : location_info := LocationInfo file_0 67 7 67 10.
  Definition loc_80 : location_info := LocationInfo file_0 67 18 67 27.
  Definition loc_81 : location_info := LocationInfo file_0 67 18 67 27.
  Definition loc_82 : location_info := LocationInfo file_0 67 19 67 22.
  Definition loc_83 : location_info := LocationInfo file_0 66 2 66 11.
  Definition loc_84 : location_info := LocationInfo file_0 66 3 66 6.
  Definition loc_85 : location_info := LocationInfo file_0 66 2 66 29.
  Definition loc_86 : location_info := LocationInfo file_0 66 2 66 11.
  Definition loc_87 : location_info := LocationInfo file_0 66 2 66 11.
  Definition loc_88 : location_info := LocationInfo file_0 66 3 66 6.
  Definition loc_89 : location_info := LocationInfo file_0 66 15 66 29.
  Definition loc_90 : location_info := LocationInfo file_0 66 15 66 23.
  Definition loc_91 : location_info := LocationInfo file_0 66 15 66 23.
  Definition loc_92 : location_info := LocationInfo file_0 66 27 66 29.
  Definition loc_93 : location_info := LocationInfo file_0 65 2 65 15.
  Definition loc_94 : location_info := LocationInfo file_0 65 3 65 15.
  Definition loc_95 : location_info := LocationInfo file_0 65 5 65 8.
  Definition loc_96 : location_info := LocationInfo file_0 63 4 63 26.
  Definition loc_97 : location_info := LocationInfo file_0 63 11 63 25.
  Definition loc_99 : location_info := LocationInfo file_0 62 6 62 15.
  Definition loc_101 : location_info := LocationInfo file_0 62 7 62 15.
  Definition loc_102 : location_info := LocationInfo file_0 62 7 62 15.
  Definition loc_103 : location_info := LocationInfo file_0 59 18 59 27.
  Definition loc_104 : location_info := LocationInfo file_0 59 18 59 27.
  Definition loc_105 : location_info := LocationInfo file_0 59 19 59 22.
  Definition loc_110 : location_info := LocationInfo file_0 96 2 96 16.
  Definition loc_111 : location_info := LocationInfo file_0 96 16 96 3.
  Definition loc_112 : location_info := LocationInfo file_0 97 2 97 35.
  Definition loc_113 : location_info := LocationInfo file_0 97 9 97 34.
  Definition loc_114 : location_info := LocationInfo file_0 97 9 97 31.
  Definition loc_115 : location_info := LocationInfo file_0 97 9 97 31.
  Definition loc_116 : location_info := LocationInfo file_0 97 32 97 33.
  Definition loc_117 : location_info := LocationInfo file_0 96 2 96 15.
  Definition loc_118 : location_info := LocationInfo file_0 96 3 96 15.
  Definition loc_119 : location_info := LocationInfo file_0 96 5 96 8.
  Definition loc_122 : location_info := LocationInfo file_0 107 2 107 20.
  Definition loc_123 : location_info := LocationInfo file_0 108 2 108 52.
  Definition loc_124 : location_info := LocationInfo file_0 109 2 109 31.
  Definition loc_125 : location_info := LocationInfo file_0 109 2 109 11.
  Definition loc_126 : location_info := LocationInfo file_0 109 3 109 6.
  Definition loc_127 : location_info := LocationInfo file_0 109 14 109 30.
  Definition loc_128 : location_info := LocationInfo file_0 109 26 109 30.
  Definition loc_129 : location_info := LocationInfo file_0 109 26 109 30.
  Definition loc_130 : location_info := LocationInfo file_0 108 2 108 11.
  Definition loc_131 : location_info := LocationInfo file_0 108 3 108 6.
  Definition loc_132 : location_info := LocationInfo file_0 108 14 108 51.
  Definition loc_133 : location_info := LocationInfo file_0 108 26 108 51.
  Definition loc_134 : location_info := LocationInfo file_0 108 27 108 43.
  Definition loc_135 : location_info := LocationInfo file_0 108 39 108 43.
  Definition loc_136 : location_info := LocationInfo file_0 108 39 108 43.
  Definition loc_137 : location_info := LocationInfo file_0 108 46 108 50.
  Definition loc_138 : location_info := LocationInfo file_0 108 46 108 50.
  Definition loc_139 : location_info := LocationInfo file_0 107 2 107 12.
  Definition loc_140 : location_info := LocationInfo file_0 107 3 107 6.
  Definition loc_141 : location_info := LocationInfo file_0 107 15 107 19.
  Definition loc_142 : location_info := LocationInfo file_0 107 15 107 19.

  (* Definition of struct [region]. *)
  Program Definition struct_region := {|
    sl_members := [
      (Some "end", it_layout size_t);
      (Some "cur", it_layout size_t);
      (Some "base", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [hyp_early_alloc_nr_pages]. *)
  Definition impl_hyp_early_alloc_nr_pages (global_mem : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 ((LocInfoE loc_4 ((LocInfoE loc_5 (use{it_layout size_t} (LocInfoE loc_6 ((LocInfoE loc_7 (global_mem)) at{struct_region} "cur")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_8 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_9 (use{void*} (LocInfoE loc_10 ((LocInfoE loc_11 (global_mem)) at{struct_region} "base")))))))) >>{IntOp size_t, IntOp size_t} (LocInfoE loc_12 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_12 (i2v 12 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_contig]. *)
  Definition impl_hyp_early_alloc_contig (global_mem global_clear_page : loc): function := {|
    f_args := [
      ("nr_pages", it_layout u32)
    ];
    f_local_vars := [
      ("i", it_layout u32);
      ("ret", it_layout size_t);
      ("p", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ it_layout size_t }
          LocInfoE loc_103 (use{it_layout size_t} (LocInfoE loc_104 ((LocInfoE loc_105 (global_mem)) at{struct_region} "cur"))) ;
        locinfo: loc_99 ;
        if: LocInfoE loc_99 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_99 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_101 (use{it_layout u32} (LocInfoE loc_102 ("nr_pages")))))))
        then
        locinfo: loc_96 ;
          Goto "#8"
        else
        locinfo: loc_17 ;
          Goto "#9"
      ]> $
      <[ "#1" :=
        locinfo: loc_17 ;
        expr: (LocInfoE loc_93 (&(LocInfoE loc_94 ((LocInfoE loc_95 (global_mem)) at{struct_region} "base")))) ;
        locinfo: loc_19 ;
        LocInfoE loc_83 ((LocInfoE loc_84 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_85 ((LocInfoE loc_86 (use{it_layout size_t} (LocInfoE loc_87 ((LocInfoE loc_88 (global_mem)) at{struct_region} "cur")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_89 ((LocInfoE loc_90 (use{it_layout u32} (LocInfoE loc_91 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_92 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_92 (i2v 12 i32))))))))) ;
        locinfo: loc_76 ;
        if: LocInfoE loc_76 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (use{it_layout size_t} (LocInfoE loc_78 ((LocInfoE loc_79 (global_mem)) at{struct_region} "cur")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_80 (use{it_layout size_t} (LocInfoE loc_81 ((LocInfoE loc_82 (global_mem)) at{struct_region} "end")))))))
        then
        locinfo: loc_68 ;
          Goto "#6"
        else
        locinfo: loc_22 ;
          Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_22 ;
        LocInfoE loc_65 ("i") <-{ it_layout u32 }
          LocInfoE loc_66 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_66 (i2v 0 i32))) ;
        locinfo: loc_23 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_60 ;
        if: LocInfoE loc_60 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_60 ((LocInfoE loc_61 (use{it_layout u32} (LocInfoE loc_62 ("i")))) <{IntOp u32, IntOp u32} (LocInfoE loc_63 (use{it_layout u32} (LocInfoE loc_64 ("nr_pages")))))))
        then
        locinfo: loc_33 ;
          Goto "#4"
        else
        locinfo: loc_24 ;
          Goto "#5"
      ]> $
      <[ "#4" :=
        locinfo: loc_33 ;
        expr: (LocInfoE loc_57 (&(LocInfoE loc_58 ((LocInfoE loc_59 (global_mem)) at{struct_region} "base")))) ;
        locinfo: loc_35 ;
        LocInfoE loc_49 ("p") <-{ it_layout size_t }
          LocInfoE loc_50 ((LocInfoE loc_51 (use{it_layout size_t} (LocInfoE loc_52 ("ret")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_53 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_53 ((LocInfoE loc_54 (use{it_layout u32} (LocInfoE loc_55 ("i")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_56 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_56 (i2v 12 i32))))))))) ;
        locinfo: loc_36 ;
        expr: (LocInfoE loc_36 (Call (LocInfoE loc_41 (global_clear_page)) [@{expr} LocInfoE loc_42 (CopyAllocId (LocInfoE loc_46 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ("p")))))) (LocInfoE loc_43 (use{void*} (LocInfoE loc_44 ((LocInfoE loc_45 (global_mem)) at{struct_region} "base"))))) ])) ;
        locinfo: loc_37 ;
        Goto "continue5"
      ]> $
      <[ "#5" :=
        locinfo: loc_24 ;
        Return (LocInfoE loc_25 (CopyAllocId (LocInfoE loc_29 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_30 (use{it_layout size_t} (LocInfoE loc_31 ("ret")))))) (LocInfoE loc_26 (use{void*} (LocInfoE loc_27 ((LocInfoE loc_28 (global_mem)) at{struct_region} "base"))))))
      ]> $
      <[ "#6" :=
        locinfo: loc_68 ;
        LocInfoE loc_71 ((LocInfoE loc_72 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_73 (use{it_layout size_t} (LocInfoE loc_74 ("ret"))) ;
        locinfo: loc_69 ;
        Return (LocInfoE loc_70 (NULL))
      ]> $
      <[ "#7" :=
        locinfo: loc_22 ;
        Goto "#2"
      ]> $
      <[ "#8" :=
        locinfo: loc_96 ;
        Return (LocInfoE loc_97 (NULL))
      ]> $
      <[ "#9" :=
        locinfo: loc_17 ;
        Goto "#1"
      ]> $
      <[ "continue5" :=
        locinfo: loc_38 ;
        LocInfoE loc_39 ("i") <-{ it_layout u32 }
          LocInfoE loc_38 ((LocInfoE loc_38 (use{it_layout u32} (LocInfoE loc_39 ("i")))) +{IntOp u32, IntOp u32} (LocInfoE loc_38 (i2v 1 u32))) ;
        locinfo: loc_23 ;
        Goto "#3"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_page]. *)
  Definition impl_hyp_early_alloc_page (global_mem global_hyp_early_alloc_contig : loc): function := {|
    f_args := [
      ("arg", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_110 ;
        expr: (LocInfoE loc_117 (&(LocInfoE loc_118 ((LocInfoE loc_119 (global_mem)) at{struct_region} "base")))) ;
        locinfo: loc_112 ;
        Return (LocInfoE loc_113 (Call (LocInfoE loc_115 (global_hyp_early_alloc_contig)) [@{expr} LocInfoE loc_116 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_116 (i2v 1 i32))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_init]. *)
  Definition impl_hyp_early_alloc_init (global_mem : loc): function := {|
    f_args := [
      ("virt", void*);
      ("size", it_layout u32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_122 ;
        LocInfoE loc_139 ((LocInfoE loc_140 (global_mem)) at{struct_region} "base") <-{ void* }
          LocInfoE loc_141 (use{void*} (LocInfoE loc_142 ("virt"))) ;
        locinfo: loc_123 ;
        LocInfoE loc_130 ((LocInfoE loc_131 (global_mem)) at{struct_region} "end") <-{ it_layout size_t }
          LocInfoE loc_132 (UnOp (CastOp $ IntOp size_t) (IntOp size_t) (LocInfoE loc_133 ((LocInfoE loc_134 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_135 (use{void*} (LocInfoE loc_136 ("virt")))))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_137 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_137 (use{it_layout u32} (LocInfoE loc_138 ("size"))))))))) ;
        locinfo: loc_124 ;
        LocInfoE loc_125 ((LocInfoE loc_126 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_127 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_128 (use{void*} (LocInfoE loc_129 ("virt"))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
