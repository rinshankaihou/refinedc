From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "linux/pkvm/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 60 2 60 40.
  Definition loc_12 : location_info := LocationInfo file_1 60 9 60 39.
  Definition loc_13 : location_info := LocationInfo file_1 60 9 60 33.
  Definition loc_14 : location_info := LocationInfo file_1 60 10 60 19.
  Definition loc_15 : location_info := LocationInfo file_1 60 10 60 19.
  Definition loc_16 : location_info := LocationInfo file_1 60 11 60 14.
  Definition loc_17 : location_info := LocationInfo file_1 60 22 60 32.
  Definition loc_18 : location_info := LocationInfo file_1 60 22 60 32.
  Definition loc_19 : location_info := LocationInfo file_1 60 23 60 26.
  Definition loc_20 : location_info := LocationInfo file_1 60 37 60 39.
  Definition loc_23 : location_info := LocationInfo file_1 73 2 73 40.
  Definition loc_24 : location_info := LocationInfo file_1 74 2 74 59.
  Definition loc_25 : location_info := LocationInfo file_1 76 2 77 26.
  Definition loc_26 : location_info := LocationInfo file_1 79 2 80 26.
  Definition loc_27 : location_info := LocationInfo file_1 82 2 82 20.
  Definition loc_28 : location_info := LocationInfo file_1 83 2 83 23.
  Definition loc_29 : location_info := LocationInfo file_1 85 2 85 13.
  Definition loc_30 : location_info := LocationInfo file_1 85 9 85 12.
  Definition loc_31 : location_info := LocationInfo file_1 85 9 85 12.
  Definition loc_32 : location_info := LocationInfo file_1 83 2 83 8.
  Definition loc_33 : location_info := LocationInfo file_1 83 2 83 8.
  Definition loc_34 : location_info := LocationInfo file_1 83 9 83 12.
  Definition loc_35 : location_info := LocationInfo file_1 83 9 83 12.
  Definition loc_36 : location_info := LocationInfo file_1 83 14 83 15.
  Definition loc_37 : location_info := LocationInfo file_1 83 17 83 21.
  Definition loc_38 : location_info := LocationInfo file_1 83 17 83 21.
  Definition loc_39 : location_info := LocationInfo file_1 82 2 82 11.
  Definition loc_40 : location_info := LocationInfo file_1 82 3 82 6.
  Definition loc_41 : location_info := LocationInfo file_1 82 2 82 19.
  Definition loc_42 : location_info := LocationInfo file_1 82 2 82 11.
  Definition loc_43 : location_info := LocationInfo file_1 82 2 82 11.
  Definition loc_44 : location_info := LocationInfo file_1 82 3 82 6.
  Definition loc_45 : location_info := LocationInfo file_1 82 15 82 19.
  Definition loc_46 : location_info := LocationInfo file_1 82 15 82 19.
  Definition loc_47 : location_info := LocationInfo file_1 80 4 80 26.
  Definition loc_48 : location_info := LocationInfo file_1 80 11 80 25.
  Definition loc_49 : location_info := LocationInfo file_1 79 2 80 26.
  Definition loc_50 : location_info := LocationInfo file_1 79 6 79 34.
  Definition loc_51 : location_info := LocationInfo file_1 79 6 79 27.
  Definition loc_52 : location_info := LocationInfo file_1 79 6 79 15.
  Definition loc_53 : location_info := LocationInfo file_1 79 6 79 15.
  Definition loc_54 : location_info := LocationInfo file_1 79 7 79 10.
  Definition loc_55 : location_info := LocationInfo file_1 79 18 79 27.
  Definition loc_56 : location_info := LocationInfo file_1 79 18 79 27.
  Definition loc_57 : location_info := LocationInfo file_1 79 19 79 22.
  Definition loc_58 : location_info := LocationInfo file_1 79 30 79 34.
  Definition loc_59 : location_info := LocationInfo file_1 79 30 79 34.
  Definition loc_60 : location_info := LocationInfo file_1 77 4 77 26.
  Definition loc_61 : location_info := LocationInfo file_1 77 11 77 25.
  Definition loc_62 : location_info := LocationInfo file_1 76 2 77 26.
  Definition loc_63 : location_info := LocationInfo file_1 76 6 76 15.
  Definition loc_65 : location_info := LocationInfo file_1 76 7 76 15.
  Definition loc_66 : location_info := LocationInfo file_1 76 7 76 15.
  Definition loc_67 : location_info := LocationInfo file_1 74 14 74 58.
  Definition loc_68 : location_info := LocationInfo file_1 74 14 74 27.
  Definition loc_69 : location_info := LocationInfo file_1 74 14 74 27.
  Definition loc_70 : location_info := LocationInfo file_1 74 28 74 37.
  Definition loc_71 : location_info := LocationInfo file_1 74 28 74 37.
  Definition loc_72 : location_info := LocationInfo file_1 74 29 74 32.
  Definition loc_73 : location_info := LocationInfo file_1 74 39 74 57.
  Definition loc_74 : location_info := LocationInfo file_1 74 47 74 57.
  Definition loc_75 : location_info := LocationInfo file_1 74 47 74 57.
  Definition loc_76 : location_info := LocationInfo file_1 74 48 74 51.
  Definition loc_79 : location_info := LocationInfo file_1 73 23 73 39.
  Definition loc_80 : location_info := LocationInfo file_1 73 24 73 32.
  Definition loc_81 : location_info := LocationInfo file_1 73 24 73 32.
  Definition loc_82 : location_info := LocationInfo file_1 73 36 73 38.
  Definition loc_87 : location_info := LocationInfo file_1 96 2 96 35.
  Definition loc_88 : location_info := LocationInfo file_1 96 9 96 34.
  Definition loc_89 : location_info := LocationInfo file_1 96 9 96 31.
  Definition loc_90 : location_info := LocationInfo file_1 96 9 96 31.
  Definition loc_91 : location_info := LocationInfo file_1 96 32 96 33.
  Definition loc_94 : location_info := LocationInfo file_1 108 2 108 35.
  Definition loc_95 : location_info := LocationInfo file_1 109 2 109 25.
  Definition loc_96 : location_info := LocationInfo file_1 110 2 110 32.
  Definition loc_97 : location_info := LocationInfo file_1 110 2 110 11.
  Definition loc_98 : location_info := LocationInfo file_1 110 3 110 6.
  Definition loc_99 : location_info := LocationInfo file_1 110 14 110 31.
  Definition loc_100 : location_info := LocationInfo file_1 110 14 110 24.
  Definition loc_101 : location_info := LocationInfo file_1 110 14 110 24.
  Definition loc_102 : location_info := LocationInfo file_1 110 15 110 18.
  Definition loc_103 : location_info := LocationInfo file_1 110 27 110 31.
  Definition loc_104 : location_info := LocationInfo file_1 110 27 110 31.
  Definition loc_105 : location_info := LocationInfo file_1 109 2 109 11.
  Definition loc_106 : location_info := LocationInfo file_1 109 3 109 6.
  Definition loc_107 : location_info := LocationInfo file_1 109 14 109 24.
  Definition loc_108 : location_info := LocationInfo file_1 109 14 109 24.
  Definition loc_109 : location_info := LocationInfo file_1 109 15 109 18.
  Definition loc_110 : location_info := LocationInfo file_1 108 2 108 12.
  Definition loc_111 : location_info := LocationInfo file_1 108 3 108 6.
  Definition loc_112 : location_info := LocationInfo file_1 108 15 108 34.
  Definition loc_113 : location_info := LocationInfo file_1 108 30 108 34.
  Definition loc_114 : location_info := LocationInfo file_1 108 30 108 34.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [region]. *)
  Program Definition struct_region := {|
    sl_members := [
      (Some "end", it_layout u64);
      (Some "cur", it_layout u64);
      (Some "base", it_layout u64)
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

  (* Definition of function [hyp_early_alloc_nr_used_pages]. *)
  Definition impl_hyp_early_alloc_nr_used_pages (global_mem : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 ((LocInfoE loc_13 ((LocInfoE loc_14 (use{IntOp u64} (LocInfoE loc_15 ((LocInfoE loc_16 (global_mem)) at{struct_region} "cur")))) -{IntOp u64, IntOp u64} (LocInfoE loc_17 (use{IntOp u64} (LocInfoE loc_18 ((LocInfoE loc_19 (global_mem)) at{struct_region} "base")))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_20 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_20 (i2v 12 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_contig]. *)
  Definition impl_hyp_early_alloc_contig (global_mem global_copy_alloc_id global_memset : loc): function := {|
    f_args := [
      ("nr_pages", it_layout u32)
    ];
    f_local_vars := [
      ("size", it_layout u64);
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "size" <-{ IntOp u64 }
          LocInfoE loc_79 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_79 ((LocInfoE loc_80 (use{IntOp u32} (LocInfoE loc_81 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_82 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_82 (i2v 12 i32))))))) ;
        "ret" <-{ PtrOp }
          LocInfoE loc_67 (Call (LocInfoE loc_69 (global_copy_alloc_id)) [@{expr} LocInfoE loc_70 (UnOp (CastOp $ IntOp uintptr_t) (IntOp u64) (LocInfoE loc_70 (use{IntOp u64} (LocInfoE loc_71 ((LocInfoE loc_72 (global_mem)) at{struct_region} "cur"))))) ;
          LocInfoE loc_73 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_74 (use{IntOp u64} (LocInfoE loc_75 ((LocInfoE loc_76 (global_mem)) at{struct_region} "base"))))) ]) ;
        locinfo: loc_63 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_63 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32, i32} (LocInfoE loc_65 (use{IntOp u32} (LocInfoE loc_66 ("nr_pages")))))
        then
        locinfo: loc_60 ;
          Goto "#5"
        else
        locinfo: loc_50 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_50 ;
        if{IntOp i32, Some "#2"}: LocInfoE loc_50 ((LocInfoE loc_51 ((LocInfoE loc_52 (use{IntOp u64} (LocInfoE loc_53 ((LocInfoE loc_54 (global_mem)) at{struct_region} "end")))) -{IntOp u64, IntOp u64} (LocInfoE loc_55 (use{IntOp u64} (LocInfoE loc_56 ((LocInfoE loc_57 (global_mem)) at{struct_region} "cur")))))) <{IntOp u64, IntOp u64, i32} (LocInfoE loc_58 (use{IntOp u64} (LocInfoE loc_59 ("size")))))
        then
        locinfo: loc_47 ;
          Goto "#3"
        else
        locinfo: loc_27 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_27 ;
        LocInfoE loc_39 ((LocInfoE loc_40 (global_mem)) at{struct_region} "cur") <-{ IntOp u64 }
          LocInfoE loc_41 ((LocInfoE loc_42 (use{IntOp u64} (LocInfoE loc_43 ((LocInfoE loc_44 (global_mem)) at{struct_region} "cur")))) +{IntOp u64, IntOp u64} (LocInfoE loc_45 (use{IntOp u64} (LocInfoE loc_46 ("size"))))) ;
        locinfo: loc_28 ;
        expr: (LocInfoE loc_28 (Call (LocInfoE loc_33 (global_memset)) [@{expr} LocInfoE loc_34 (use{PtrOp} (LocInfoE loc_35 ("ret"))) ;
        LocInfoE loc_36 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_36 (i2v 0 i32))) ;
        LocInfoE loc_37 (use{IntOp u64} (LocInfoE loc_38 ("size"))) ])) ;
        locinfo: loc_29 ;
        Return (LocInfoE loc_30 (use{PtrOp} (LocInfoE loc_31 ("ret"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_47 ;
        Return (LocInfoE loc_48 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_27 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_60 ;
        Return (LocInfoE loc_61 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_50 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_page]. *)
  Definition impl_hyp_early_alloc_page (global_hyp_early_alloc_contig : loc): function := {|
    f_args := [
      ("arg", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_87 ;
        Return (LocInfoE loc_88 (Call (LocInfoE loc_90 (global_hyp_early_alloc_contig)) [@{expr} LocInfoE loc_91 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_91 (i2v 1 i32))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_init]. *)
  Definition impl_hyp_early_alloc_init (global_mem : loc): function := {|
    f_args := [
      ("virt", void*);
      ("size", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_94 ;
        LocInfoE loc_110 ((LocInfoE loc_111 (global_mem)) at{struct_region} "base") <-{ IntOp u64 }
          LocInfoE loc_112 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_113 (use{PtrOp} (LocInfoE loc_114 ("virt"))))) ;
        locinfo: loc_95 ;
        LocInfoE loc_105 ((LocInfoE loc_106 (global_mem)) at{struct_region} "cur") <-{ IntOp u64 }
          LocInfoE loc_107 (use{IntOp u64} (LocInfoE loc_108 ((LocInfoE loc_109 (global_mem)) at{struct_region} "base"))) ;
        locinfo: loc_96 ;
        LocInfoE loc_97 ((LocInfoE loc_98 (global_mem)) at{struct_region} "end") <-{ IntOp u64 }
          LocInfoE loc_99 ((LocInfoE loc_100 (use{IntOp u64} (LocInfoE loc_101 ((LocInfoE loc_102 (global_mem)) at{struct_region} "base")))) +{IntOp u64, IntOp u64} (LocInfoE loc_103 (use{IntOp u64} (LocInfoE loc_104 ("size"))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
