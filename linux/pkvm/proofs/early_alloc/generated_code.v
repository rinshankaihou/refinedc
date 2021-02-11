From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/pkvm/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 41 2 41 52.
  Definition loc_3 : location_info := LocationInfo file_0 41 9 41 51.
  Definition loc_4 : location_info := LocationInfo file_0 41 9 41 45.
  Definition loc_5 : location_info := LocationInfo file_0 41 10 41 19.
  Definition loc_6 : location_info := LocationInfo file_0 41 10 41 19.
  Definition loc_7 : location_info := LocationInfo file_0 41 11 41 14.
  Definition loc_8 : location_info := LocationInfo file_0 41 22 41 44.
  Definition loc_9 : location_info := LocationInfo file_0 41 34 41 44.
  Definition loc_10 : location_info := LocationInfo file_0 41 34 41 44.
  Definition loc_11 : location_info := LocationInfo file_0 41 35 41 38.
  Definition loc_12 : location_info := LocationInfo file_0 41 49 41 51.
  Definition loc_15 : location_info := LocationInfo file_0 57 2 57 31.
  Definition loc_16 : location_info := LocationInfo file_0 60 2 61 26.
  Definition loc_17 : location_info := LocationInfo file_0 63 2 63 30.
  Definition loc_18 : location_info := LocationInfo file_0 64 2 67 3.
  Definition loc_19 : location_info := LocationInfo file_0 75 2 75 67.
  Definition loc_20 : location_info := LocationInfo file_0 75 9 75 66.
  Definition loc_21 : location_info := LocationInfo file_0 75 35 75 47.
  Definition loc_22 : location_info := LocationInfo file_0 75 35 75 47.
  Definition loc_23 : location_info := LocationInfo file_0 75 37 75 40.
  Definition loc_24 : location_info := LocationInfo file_0 75 51 75 65.
  Definition loc_25 : location_info := LocationInfo file_0 75 61 75 64.
  Definition loc_26 : location_info := LocationInfo file_0 75 61 75 64.
  Definition loc_27 : location_info := LocationInfo file_0 64 29 67 3.
  Definition loc_28 : location_info := LocationInfo file_0 65 4 65 20.
  Definition loc_29 : location_info := LocationInfo file_0 66 4 66 26.
  Definition loc_30 : location_info := LocationInfo file_0 66 11 66 25.
  Definition loc_31 : location_info := LocationInfo file_0 65 4 65 13.
  Definition loc_32 : location_info := LocationInfo file_0 65 5 65 8.
  Definition loc_33 : location_info := LocationInfo file_0 65 16 65 19.
  Definition loc_34 : location_info := LocationInfo file_0 65 16 65 19.
  Definition loc_36 : location_info := LocationInfo file_0 64 6 64 27.
  Definition loc_37 : location_info := LocationInfo file_0 64 6 64 15.
  Definition loc_38 : location_info := LocationInfo file_0 64 6 64 15.
  Definition loc_39 : location_info := LocationInfo file_0 64 7 64 10.
  Definition loc_40 : location_info := LocationInfo file_0 64 18 64 27.
  Definition loc_41 : location_info := LocationInfo file_0 64 18 64 27.
  Definition loc_42 : location_info := LocationInfo file_0 64 19 64 22.
  Definition loc_43 : location_info := LocationInfo file_0 63 2 63 11.
  Definition loc_44 : location_info := LocationInfo file_0 63 3 63 6.
  Definition loc_45 : location_info := LocationInfo file_0 63 2 63 29.
  Definition loc_46 : location_info := LocationInfo file_0 63 2 63 11.
  Definition loc_47 : location_info := LocationInfo file_0 63 2 63 11.
  Definition loc_48 : location_info := LocationInfo file_0 63 3 63 6.
  Definition loc_49 : location_info := LocationInfo file_0 63 15 63 29.
  Definition loc_50 : location_info := LocationInfo file_0 63 15 63 23.
  Definition loc_51 : location_info := LocationInfo file_0 63 15 63 23.
  Definition loc_52 : location_info := LocationInfo file_0 63 27 63 29.
  Definition loc_53 : location_info := LocationInfo file_0 61 4 61 26.
  Definition loc_54 : location_info := LocationInfo file_0 61 11 61 25.
  Definition loc_56 : location_info := LocationInfo file_0 60 6 60 15.
  Definition loc_58 : location_info := LocationInfo file_0 60 7 60 15.
  Definition loc_59 : location_info := LocationInfo file_0 60 7 60 15.
  Definition loc_60 : location_info := LocationInfo file_0 57 18 57 27.
  Definition loc_61 : location_info := LocationInfo file_0 57 18 57 27.
  Definition loc_62 : location_info := LocationInfo file_0 57 19 57 22.
  Definition loc_67 : location_info := LocationInfo file_0 85 2 85 16.
  Definition loc_68 : location_info := LocationInfo file_0 85 16 85 3.
  Definition loc_69 : location_info := LocationInfo file_0 86 2 86 35.
  Definition loc_70 : location_info := LocationInfo file_0 86 9 86 34.
  Definition loc_71 : location_info := LocationInfo file_0 86 9 86 31.
  Definition loc_72 : location_info := LocationInfo file_0 86 9 86 31.
  Definition loc_73 : location_info := LocationInfo file_0 86 32 86 33.
  Definition loc_74 : location_info := LocationInfo file_0 85 2 85 15.
  Definition loc_75 : location_info := LocationInfo file_0 85 3 85 15.
  Definition loc_76 : location_info := LocationInfo file_0 85 5 85 8.
  Definition loc_79 : location_info := LocationInfo file_0 96 2 96 20.
  Definition loc_80 : location_info := LocationInfo file_0 97 2 97 52.
  Definition loc_81 : location_info := LocationInfo file_0 98 2 98 31.
  Definition loc_82 : location_info := LocationInfo file_0 98 2 98 11.
  Definition loc_83 : location_info := LocationInfo file_0 98 3 98 6.
  Definition loc_84 : location_info := LocationInfo file_0 98 14 98 30.
  Definition loc_85 : location_info := LocationInfo file_0 98 26 98 30.
  Definition loc_86 : location_info := LocationInfo file_0 98 26 98 30.
  Definition loc_87 : location_info := LocationInfo file_0 97 2 97 11.
  Definition loc_88 : location_info := LocationInfo file_0 97 3 97 6.
  Definition loc_89 : location_info := LocationInfo file_0 97 14 97 51.
  Definition loc_90 : location_info := LocationInfo file_0 97 26 97 51.
  Definition loc_91 : location_info := LocationInfo file_0 97 27 97 43.
  Definition loc_92 : location_info := LocationInfo file_0 97 39 97 43.
  Definition loc_93 : location_info := LocationInfo file_0 97 39 97 43.
  Definition loc_94 : location_info := LocationInfo file_0 97 46 97 50.
  Definition loc_95 : location_info := LocationInfo file_0 97 46 97 50.
  Definition loc_96 : location_info := LocationInfo file_0 96 2 96 12.
  Definition loc_97 : location_info := LocationInfo file_0 96 3 96 6.
  Definition loc_98 : location_info := LocationInfo file_0 96 15 96 19.
  Definition loc_99 : location_info := LocationInfo file_0 96 15 96 19.

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
  Definition impl_hyp_early_alloc_page (global_mem global_hyp_early_alloc_contig : loc): function := {|
    f_args := [
      ("arg", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_67 ;
        expr: (LocInfoE loc_74 (&(LocInfoE loc_75 ((LocInfoE loc_76 (global_mem)) at{struct_region} "base")))) ;
        locinfo: loc_69 ;
        Return (LocInfoE loc_70 (Call (LocInfoE loc_72 (global_hyp_early_alloc_contig)) [@{expr} LocInfoE loc_73 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_73 (i2v 1 i32))) ]))
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
        locinfo: loc_79 ;
        LocInfoE loc_96 ((LocInfoE loc_97 (global_mem)) at{struct_region} "base") <-{ void* }
          LocInfoE loc_98 (use{void*} (LocInfoE loc_99 ("virt"))) ;
        locinfo: loc_80 ;
        LocInfoE loc_87 ((LocInfoE loc_88 (global_mem)) at{struct_region} "end") <-{ it_layout size_t }
          LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (IntOp size_t) (LocInfoE loc_90 ((LocInfoE loc_91 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_92 (use{void*} (LocInfoE loc_93 ("virt")))))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_94 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_94 (use{it_layout u32} (LocInfoE loc_95 ("size"))))))))) ;
        locinfo: loc_81 ;
        LocInfoE loc_82 ((LocInfoE loc_83 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_84 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_85 (use{void*} (LocInfoE loc_86 ("virt"))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
