From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/pkvm/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 38 2 38 52.
  Definition loc_3 : location_info := LocationInfo file_0 38 9 38 51.
  Definition loc_4 : location_info := LocationInfo file_0 38 9 38 45.
  Definition loc_5 : location_info := LocationInfo file_0 38 10 38 19.
  Definition loc_6 : location_info := LocationInfo file_0 38 10 38 19.
  Definition loc_7 : location_info := LocationInfo file_0 38 11 38 14.
  Definition loc_8 : location_info := LocationInfo file_0 38 22 38 44.
  Definition loc_9 : location_info := LocationInfo file_0 38 34 38 44.
  Definition loc_10 : location_info := LocationInfo file_0 38 34 38 44.
  Definition loc_11 : location_info := LocationInfo file_0 38 35 38 38.
  Definition loc_12 : location_info := LocationInfo file_0 38 49 38 51.
  Definition loc_15 : location_info := LocationInfo file_0 53 2 53 31.
  Definition loc_16 : location_info := LocationInfo file_0 56 2 57 26.
  Definition loc_17 : location_info := LocationInfo file_0 59 2 59 30.
  Definition loc_18 : location_info := LocationInfo file_0 60 2 63 3.
  Definition loc_19 : location_info := LocationInfo file_0 71 2 71 67.
  Definition loc_20 : location_info := LocationInfo file_0 71 9 71 66.
  Definition loc_21 : location_info := LocationInfo file_0 71 35 71 47.
  Definition loc_22 : location_info := LocationInfo file_0 71 35 71 47.
  Definition loc_23 : location_info := LocationInfo file_0 71 37 71 40.
  Definition loc_24 : location_info := LocationInfo file_0 71 51 71 65.
  Definition loc_25 : location_info := LocationInfo file_0 71 61 71 64.
  Definition loc_26 : location_info := LocationInfo file_0 71 61 71 64.
  Definition loc_27 : location_info := LocationInfo file_0 60 29 63 3.
  Definition loc_28 : location_info := LocationInfo file_0 61 4 61 20.
  Definition loc_29 : location_info := LocationInfo file_0 62 4 62 26.
  Definition loc_30 : location_info := LocationInfo file_0 62 11 62 25.
  Definition loc_31 : location_info := LocationInfo file_0 61 4 61 13.
  Definition loc_32 : location_info := LocationInfo file_0 61 5 61 8.
  Definition loc_33 : location_info := LocationInfo file_0 61 16 61 19.
  Definition loc_34 : location_info := LocationInfo file_0 61 16 61 19.
  Definition loc_36 : location_info := LocationInfo file_0 60 6 60 27.
  Definition loc_37 : location_info := LocationInfo file_0 60 6 60 15.
  Definition loc_38 : location_info := LocationInfo file_0 60 6 60 15.
  Definition loc_39 : location_info := LocationInfo file_0 60 7 60 10.
  Definition loc_40 : location_info := LocationInfo file_0 60 18 60 27.
  Definition loc_41 : location_info := LocationInfo file_0 60 18 60 27.
  Definition loc_42 : location_info := LocationInfo file_0 60 19 60 22.
  Definition loc_43 : location_info := LocationInfo file_0 59 2 59 11.
  Definition loc_44 : location_info := LocationInfo file_0 59 3 59 6.
  Definition loc_45 : location_info := LocationInfo file_0 59 2 59 29.
  Definition loc_46 : location_info := LocationInfo file_0 59 2 59 11.
  Definition loc_47 : location_info := LocationInfo file_0 59 2 59 11.
  Definition loc_48 : location_info := LocationInfo file_0 59 3 59 6.
  Definition loc_49 : location_info := LocationInfo file_0 59 15 59 29.
  Definition loc_50 : location_info := LocationInfo file_0 59 15 59 23.
  Definition loc_51 : location_info := LocationInfo file_0 59 15 59 23.
  Definition loc_52 : location_info := LocationInfo file_0 59 27 59 29.
  Definition loc_53 : location_info := LocationInfo file_0 57 4 57 26.
  Definition loc_54 : location_info := LocationInfo file_0 57 11 57 25.
  Definition loc_56 : location_info := LocationInfo file_0 56 6 56 15.
  Definition loc_58 : location_info := LocationInfo file_0 56 7 56 15.
  Definition loc_59 : location_info := LocationInfo file_0 56 7 56 15.
  Definition loc_60 : location_info := LocationInfo file_0 53 18 53 27.
  Definition loc_61 : location_info := LocationInfo file_0 53 18 53 27.
  Definition loc_62 : location_info := LocationInfo file_0 53 19 53 22.
  Definition loc_67 : location_info := LocationInfo file_0 80 2 80 35.
  Definition loc_68 : location_info := LocationInfo file_0 80 9 80 34.
  Definition loc_69 : location_info := LocationInfo file_0 80 9 80 31.
  Definition loc_70 : location_info := LocationInfo file_0 80 9 80 31.
  Definition loc_71 : location_info := LocationInfo file_0 80 32 80 33.
  Definition loc_74 : location_info := LocationInfo file_0 89 2 89 20.
  Definition loc_75 : location_info := LocationInfo file_0 90 2 90 52.
  Definition loc_76 : location_info := LocationInfo file_0 91 2 91 31.
  Definition loc_77 : location_info := LocationInfo file_0 91 2 91 11.
  Definition loc_78 : location_info := LocationInfo file_0 91 3 91 6.
  Definition loc_79 : location_info := LocationInfo file_0 91 14 91 30.
  Definition loc_80 : location_info := LocationInfo file_0 91 26 91 30.
  Definition loc_81 : location_info := LocationInfo file_0 91 26 91 30.
  Definition loc_82 : location_info := LocationInfo file_0 90 2 90 11.
  Definition loc_83 : location_info := LocationInfo file_0 90 3 90 6.
  Definition loc_84 : location_info := LocationInfo file_0 90 14 90 51.
  Definition loc_85 : location_info := LocationInfo file_0 90 26 90 51.
  Definition loc_86 : location_info := LocationInfo file_0 90 27 90 43.
  Definition loc_87 : location_info := LocationInfo file_0 90 39 90 43.
  Definition loc_88 : location_info := LocationInfo file_0 90 39 90 43.
  Definition loc_89 : location_info := LocationInfo file_0 90 46 90 50.
  Definition loc_90 : location_info := LocationInfo file_0 90 46 90 50.
  Definition loc_91 : location_info := LocationInfo file_0 89 2 89 12.
  Definition loc_92 : location_info := LocationInfo file_0 89 3 89 6.
  Definition loc_93 : location_info := LocationInfo file_0 89 15 89 19.
  Definition loc_94 : location_info := LocationInfo file_0 89 15 89 19.

  (* Definition of struct [region]. *)
  Program Definition struct_region := {|
    sl_members := [
      (Some "base", void*);
      (Some "end", it_layout size_t);
      (Some "cur", it_layout size_t)
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
  Definition impl_hyp_early_alloc_contig (global_mem : loc): function := {|
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
          LocInfoE loc_60 (use{it_layout size_t} (LocInfoE loc_61 ((LocInfoE loc_62 (global_mem)) at{struct_region} "cur"))) ;
        locinfo: loc_56 ;
        if: LocInfoE loc_56 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_56 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_58 (use{it_layout u32} (LocInfoE loc_59 ("nr_pages")))))))
        then
        locinfo: loc_53 ;
          Goto "#5"
        else
        locinfo: loc_17 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_17 ;
        LocInfoE loc_43 ((LocInfoE loc_44 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_45 ((LocInfoE loc_46 (use{it_layout size_t} (LocInfoE loc_47 ((LocInfoE loc_48 (global_mem)) at{struct_region} "cur")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_49 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_49 ((LocInfoE loc_50 (use{it_layout u32} (LocInfoE loc_51 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_52 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_52 (i2v 12 i32))))))))) ;
        locinfo: loc_36 ;
        if: LocInfoE loc_36 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_36 ((LocInfoE loc_37 (use{it_layout size_t} (LocInfoE loc_38 ((LocInfoE loc_39 (global_mem)) at{struct_region} "cur")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_40 (use{it_layout size_t} (LocInfoE loc_41 ((LocInfoE loc_42 (global_mem)) at{struct_region} "end")))))))
        then
        locinfo: loc_28 ;
          Goto "#3"
        else
        locinfo: loc_19 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_19 ;
        Return (LocInfoE loc_20 (CopyAllocId (LocInfoE loc_24 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_25 (use{it_layout size_t} (LocInfoE loc_26 ("ret")))))) (LocInfoE loc_21 (use{void*} (LocInfoE loc_22 ((LocInfoE loc_23 (global_mem)) at{struct_region} "base"))))))
      ]> $
      <[ "#3" :=
        locinfo: loc_28 ;
        LocInfoE loc_31 ((LocInfoE loc_32 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_33 (use{it_layout size_t} (LocInfoE loc_34 ("ret"))) ;
        locinfo: loc_29 ;
        Return (LocInfoE loc_30 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_19 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_53 ;
        Return (LocInfoE loc_54 (NULL))
      ]> $
      <[ "#6" :=
        locinfo: loc_17 ;
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
        locinfo: loc_67 ;
        Return (LocInfoE loc_68 (Call (LocInfoE loc_70 (global_hyp_early_alloc_contig)) [@{expr} LocInfoE loc_71 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_71 (i2v 1 i32))) ]))
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
        locinfo: loc_74 ;
        LocInfoE loc_91 ((LocInfoE loc_92 (global_mem)) at{struct_region} "base") <-{ void* }
          LocInfoE loc_93 (use{void*} (LocInfoE loc_94 ("virt"))) ;
        locinfo: loc_75 ;
        LocInfoE loc_82 ((LocInfoE loc_83 (global_mem)) at{struct_region} "end") <-{ it_layout size_t }
          LocInfoE loc_84 (UnOp (CastOp $ IntOp size_t) (IntOp size_t) (LocInfoE loc_85 ((LocInfoE loc_86 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ("virt")))))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_89 (use{it_layout u32} (LocInfoE loc_90 ("size"))))))))) ;
        locinfo: loc_76 ;
        LocInfoE loc_77 ((LocInfoE loc_78 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_79 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_80 (use{void*} (LocInfoE loc_81 ("virt"))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
