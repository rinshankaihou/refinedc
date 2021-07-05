From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/pkvm/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 60 2 60 40.
  Definition loc_3 : location_info := LocationInfo file_0 60 9 60 39.
  Definition loc_4 : location_info := LocationInfo file_0 60 9 60 33.
  Definition loc_5 : location_info := LocationInfo file_0 60 10 60 19.
  Definition loc_6 : location_info := LocationInfo file_0 60 10 60 19.
  Definition loc_7 : location_info := LocationInfo file_0 60 11 60 14.
  Definition loc_8 : location_info := LocationInfo file_0 60 22 60 32.
  Definition loc_9 : location_info := LocationInfo file_0 60 22 60 32.
  Definition loc_10 : location_info := LocationInfo file_0 60 23 60 26.
  Definition loc_11 : location_info := LocationInfo file_0 60 37 60 39.
  Definition loc_14 : location_info := LocationInfo file_0 73 2 73 40.
  Definition loc_15 : location_info := LocationInfo file_0 74 2 74 73.
  Definition loc_16 : location_info := LocationInfo file_0 76 2 77 26.
  Definition loc_17 : location_info := LocationInfo file_0 79 2 80 26.
  Definition loc_18 : location_info := LocationInfo file_0 82 2 82 20.
  Definition loc_19 : location_info := LocationInfo file_0 83 2 83 23.
  Definition loc_20 : location_info := LocationInfo file_0 85 2 85 13.
  Definition loc_21 : location_info := LocationInfo file_0 85 9 85 12.
  Definition loc_22 : location_info := LocationInfo file_0 85 9 85 12.
  Definition loc_23 : location_info := LocationInfo file_0 83 2 83 8.
  Definition loc_24 : location_info := LocationInfo file_0 83 2 83 8.
  Definition loc_25 : location_info := LocationInfo file_0 83 9 83 12.
  Definition loc_26 : location_info := LocationInfo file_0 83 9 83 12.
  Definition loc_27 : location_info := LocationInfo file_0 83 14 83 15.
  Definition loc_28 : location_info := LocationInfo file_0 83 17 83 21.
  Definition loc_29 : location_info := LocationInfo file_0 83 17 83 21.
  Definition loc_30 : location_info := LocationInfo file_0 82 2 82 11.
  Definition loc_31 : location_info := LocationInfo file_0 82 3 82 6.
  Definition loc_32 : location_info := LocationInfo file_0 82 2 82 19.
  Definition loc_33 : location_info := LocationInfo file_0 82 2 82 11.
  Definition loc_34 : location_info := LocationInfo file_0 82 2 82 11.
  Definition loc_35 : location_info := LocationInfo file_0 82 3 82 6.
  Definition loc_36 : location_info := LocationInfo file_0 82 15 82 19.
  Definition loc_37 : location_info := LocationInfo file_0 82 15 82 19.
  Definition loc_38 : location_info := LocationInfo file_0 80 4 80 26.
  Definition loc_39 : location_info := LocationInfo file_0 80 11 80 25.
  Definition loc_41 : location_info := LocationInfo file_0 79 6 79 34.
  Definition loc_42 : location_info := LocationInfo file_0 79 6 79 27.
  Definition loc_43 : location_info := LocationInfo file_0 79 6 79 15.
  Definition loc_44 : location_info := LocationInfo file_0 79 6 79 15.
  Definition loc_45 : location_info := LocationInfo file_0 79 7 79 10.
  Definition loc_46 : location_info := LocationInfo file_0 79 18 79 27.
  Definition loc_47 : location_info := LocationInfo file_0 79 18 79 27.
  Definition loc_48 : location_info := LocationInfo file_0 79 19 79 22.
  Definition loc_49 : location_info := LocationInfo file_0 79 30 79 34.
  Definition loc_50 : location_info := LocationInfo file_0 79 30 79 34.
  Definition loc_51 : location_info := LocationInfo file_0 77 4 77 26.
  Definition loc_52 : location_info := LocationInfo file_0 77 11 77 25.
  Definition loc_54 : location_info := LocationInfo file_0 76 6 76 15.
  Definition loc_56 : location_info := LocationInfo file_0 76 7 76 15.
  Definition loc_57 : location_info := LocationInfo file_0 76 7 76 15.
  Definition loc_58 : location_info := LocationInfo file_0 74 14 74 72.
  Definition loc_59 : location_info := LocationInfo file_0 74 14 74 37.
  Definition loc_60 : location_info := LocationInfo file_0 74 38 74 49.
  Definition loc_61 : location_info := LocationInfo file_0 74 38 74 49.
  Definition loc_62 : location_info := LocationInfo file_0 74 40 74 43.
  Definition loc_63 : location_info := LocationInfo file_0 74 51 74 71.
  Definition loc_64 : location_info := LocationInfo file_0 74 60 74 70.
  Definition loc_65 : location_info := LocationInfo file_0 74 60 74 70.
  Definition loc_66 : location_info := LocationInfo file_0 74 61 74 64.
  Definition loc_69 : location_info := LocationInfo file_0 73 23 73 39.
  Definition loc_70 : location_info := LocationInfo file_0 73 24 73 32.
  Definition loc_71 : location_info := LocationInfo file_0 73 24 73 32.
  Definition loc_72 : location_info := LocationInfo file_0 73 36 73 38.
  Definition loc_77 : location_info := LocationInfo file_0 96 2 96 35.
  Definition loc_78 : location_info := LocationInfo file_0 96 9 96 34.
  Definition loc_79 : location_info := LocationInfo file_0 96 9 96 31.
  Definition loc_80 : location_info := LocationInfo file_0 96 9 96 31.
  Definition loc_81 : location_info := LocationInfo file_0 96 32 96 33.
  Definition loc_84 : location_info := LocationInfo file_0 108 2 108 35.
  Definition loc_85 : location_info := LocationInfo file_0 109 2 109 25.
  Definition loc_86 : location_info := LocationInfo file_0 110 2 110 32.
  Definition loc_87 : location_info := LocationInfo file_0 110 2 110 11.
  Definition loc_88 : location_info := LocationInfo file_0 110 3 110 6.
  Definition loc_89 : location_info := LocationInfo file_0 110 14 110 31.
  Definition loc_90 : location_info := LocationInfo file_0 110 14 110 24.
  Definition loc_91 : location_info := LocationInfo file_0 110 14 110 24.
  Definition loc_92 : location_info := LocationInfo file_0 110 15 110 18.
  Definition loc_93 : location_info := LocationInfo file_0 110 27 110 31.
  Definition loc_94 : location_info := LocationInfo file_0 110 27 110 31.
  Definition loc_95 : location_info := LocationInfo file_0 109 2 109 11.
  Definition loc_96 : location_info := LocationInfo file_0 109 3 109 6.
  Definition loc_97 : location_info := LocationInfo file_0 109 14 109 24.
  Definition loc_98 : location_info := LocationInfo file_0 109 14 109 24.
  Definition loc_99 : location_info := LocationInfo file_0 109 15 109 18.
  Definition loc_100 : location_info := LocationInfo file_0 108 2 108 12.
  Definition loc_101 : location_info := LocationInfo file_0 108 3 108 6.
  Definition loc_102 : location_info := LocationInfo file_0 108 15 108 34.
  Definition loc_103 : location_info := LocationInfo file_0 108 30 108 34.
  Definition loc_104 : location_info := LocationInfo file_0 108 30 108 34.

  (* Definition of struct [region]. *)
  Program Definition struct_region := {|
    sl_members := [
      (Some "end", it_layout u64);
      (Some "cur", it_layout u64);
      (Some "base", it_layout u64)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [hyp_early_alloc_nr_used_pages]. *)
  Definition impl_hyp_early_alloc_nr_used_pages (global_mem : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 ((LocInfoE loc_4 ((LocInfoE loc_5 (use{it_layout u64} (LocInfoE loc_6 ((LocInfoE loc_7 (global_mem)) at{struct_region} "cur")))) -{IntOp u64, IntOp u64} (LocInfoE loc_8 (use{it_layout u64} (LocInfoE loc_9 ((LocInfoE loc_10 (global_mem)) at{struct_region} "base")))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_11 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_11 (i2v 12 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_contig]. *)
  Definition impl_hyp_early_alloc_contig (global_mem global_memset : loc): function := {|
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
        "size" <-{ it_layout u64 }
          LocInfoE loc_69 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_69 ((LocInfoE loc_70 (use{it_layout u32} (LocInfoE loc_71 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_72 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_72 (i2v 12 i32))))))) ;
        "ret" <-{ void* }
          LocInfoE loc_58 (CopyAllocId (IntOp u64) (LocInfoE loc_60 (use{it_layout u64} (LocInfoE loc_61 ((LocInfoE loc_62 (global_mem)) at{struct_region} "cur")))) (LocInfoE loc_63 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_64 (use{it_layout u64} (LocInfoE loc_65 ((LocInfoE loc_66 (global_mem)) at{struct_region} "base"))))))) ;
        locinfo: loc_54 ;
        if: LocInfoE loc_54 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_54 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_56 (use{it_layout u32} (LocInfoE loc_57 ("nr_pages")))))))
        then
        locinfo: loc_51 ;
          Goto "#5"
        else
        locinfo: loc_41 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_41 ;
        if: LocInfoE loc_41 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_41 ((LocInfoE loc_42 ((LocInfoE loc_43 (use{it_layout u64} (LocInfoE loc_44 ((LocInfoE loc_45 (global_mem)) at{struct_region} "end")))) -{IntOp u64, IntOp u64} (LocInfoE loc_46 (use{it_layout u64} (LocInfoE loc_47 ((LocInfoE loc_48 (global_mem)) at{struct_region} "cur")))))) <{IntOp u64, IntOp u64} (LocInfoE loc_49 (use{it_layout u64} (LocInfoE loc_50 ("size")))))))
        then
        locinfo: loc_38 ;
          Goto "#3"
        else
        locinfo: loc_18 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_18 ;
        LocInfoE loc_30 ((LocInfoE loc_31 (global_mem)) at{struct_region} "cur") <-{ it_layout u64 }
          LocInfoE loc_32 ((LocInfoE loc_33 (use{it_layout u64} (LocInfoE loc_34 ((LocInfoE loc_35 (global_mem)) at{struct_region} "cur")))) +{IntOp u64, IntOp u64} (LocInfoE loc_36 (use{it_layout u64} (LocInfoE loc_37 ("size"))))) ;
        locinfo: loc_19 ;
        expr: (LocInfoE loc_19 (Call (LocInfoE loc_24 (global_memset)) [@{expr} LocInfoE loc_25 (use{void*} (LocInfoE loc_26 ("ret"))) ;
        LocInfoE loc_27 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_27 (i2v 0 i32))) ;
        LocInfoE loc_28 (use{it_layout u64} (LocInfoE loc_29 ("size"))) ])) ;
        locinfo: loc_20 ;
        Return (LocInfoE loc_21 (use{void*} (LocInfoE loc_22 ("ret"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_38 ;
        Return (LocInfoE loc_39 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_18 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_51 ;
        Return (LocInfoE loc_52 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_41 ;
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
        locinfo: loc_77 ;
        Return (LocInfoE loc_78 (Call (LocInfoE loc_80 (global_hyp_early_alloc_contig)) [@{expr} LocInfoE loc_81 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_81 (i2v 1 i32))) ]))
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
        locinfo: loc_84 ;
        LocInfoE loc_100 ((LocInfoE loc_101 (global_mem)) at{struct_region} "base") <-{ it_layout u64 }
          LocInfoE loc_102 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_103 (use{void*} (LocInfoE loc_104 ("virt"))))) ;
        locinfo: loc_85 ;
        LocInfoE loc_95 ((LocInfoE loc_96 (global_mem)) at{struct_region} "cur") <-{ it_layout u64 }
          LocInfoE loc_97 (use{it_layout u64} (LocInfoE loc_98 ((LocInfoE loc_99 (global_mem)) at{struct_region} "base"))) ;
        locinfo: loc_86 ;
        LocInfoE loc_87 ((LocInfoE loc_88 (global_mem)) at{struct_region} "end") <-{ it_layout u64 }
          LocInfoE loc_89 ((LocInfoE loc_90 (use{it_layout u64} (LocInfoE loc_91 ((LocInfoE loc_92 (global_mem)) at{struct_region} "base")))) +{IntOp u64, IntOp u64} (LocInfoE loc_93 (use{it_layout u64} (LocInfoE loc_94 ("size"))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
