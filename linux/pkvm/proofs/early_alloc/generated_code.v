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
  Definition loc_15 : location_info := LocationInfo file_0 62 2 62 31.
  Definition loc_16 : location_info := LocationInfo file_0 65 2 66 26.
  Definition loc_17 : location_info := LocationInfo file_0 68 2 68 16.
  Definition loc_18 : location_info := LocationInfo file_0 68 16 68 3.
  Definition loc_19 : location_info := LocationInfo file_0 69 2 69 30.
  Definition loc_20 : location_info := LocationInfo file_0 70 2 73 3.
  Definition loc_21 : location_info := LocationInfo file_0 81 2 81 67.
  Definition loc_22 : location_info := LocationInfo file_0 81 9 81 66.
  Definition loc_23 : location_info := LocationInfo file_0 81 35 81 47.
  Definition loc_24 : location_info := LocationInfo file_0 81 35 81 47.
  Definition loc_25 : location_info := LocationInfo file_0 81 37 81 40.
  Definition loc_26 : location_info := LocationInfo file_0 81 51 81 65.
  Definition loc_27 : location_info := LocationInfo file_0 81 61 81 64.
  Definition loc_28 : location_info := LocationInfo file_0 81 61 81 64.
  Definition loc_29 : location_info := LocationInfo file_0 70 29 73 3.
  Definition loc_30 : location_info := LocationInfo file_0 71 4 71 20.
  Definition loc_31 : location_info := LocationInfo file_0 72 4 72 26.
  Definition loc_32 : location_info := LocationInfo file_0 72 11 72 25.
  Definition loc_33 : location_info := LocationInfo file_0 71 4 71 13.
  Definition loc_34 : location_info := LocationInfo file_0 71 5 71 8.
  Definition loc_35 : location_info := LocationInfo file_0 71 16 71 19.
  Definition loc_36 : location_info := LocationInfo file_0 71 16 71 19.
  Definition loc_38 : location_info := LocationInfo file_0 70 6 70 27.
  Definition loc_39 : location_info := LocationInfo file_0 70 6 70 15.
  Definition loc_40 : location_info := LocationInfo file_0 70 6 70 15.
  Definition loc_41 : location_info := LocationInfo file_0 70 7 70 10.
  Definition loc_42 : location_info := LocationInfo file_0 70 18 70 27.
  Definition loc_43 : location_info := LocationInfo file_0 70 18 70 27.
  Definition loc_44 : location_info := LocationInfo file_0 70 19 70 22.
  Definition loc_45 : location_info := LocationInfo file_0 69 2 69 11.
  Definition loc_46 : location_info := LocationInfo file_0 69 3 69 6.
  Definition loc_47 : location_info := LocationInfo file_0 69 2 69 29.
  Definition loc_48 : location_info := LocationInfo file_0 69 2 69 11.
  Definition loc_49 : location_info := LocationInfo file_0 69 2 69 11.
  Definition loc_50 : location_info := LocationInfo file_0 69 3 69 6.
  Definition loc_51 : location_info := LocationInfo file_0 69 15 69 29.
  Definition loc_52 : location_info := LocationInfo file_0 69 15 69 23.
  Definition loc_53 : location_info := LocationInfo file_0 69 15 69 23.
  Definition loc_54 : location_info := LocationInfo file_0 69 27 69 29.
  Definition loc_55 : location_info := LocationInfo file_0 68 2 68 15.
  Definition loc_56 : location_info := LocationInfo file_0 68 3 68 15.
  Definition loc_57 : location_info := LocationInfo file_0 68 5 68 8.
  Definition loc_58 : location_info := LocationInfo file_0 66 4 66 26.
  Definition loc_59 : location_info := LocationInfo file_0 66 11 66 25.
  Definition loc_61 : location_info := LocationInfo file_0 65 6 65 15.
  Definition loc_63 : location_info := LocationInfo file_0 65 7 65 15.
  Definition loc_64 : location_info := LocationInfo file_0 65 7 65 15.
  Definition loc_65 : location_info := LocationInfo file_0 62 18 62 27.
  Definition loc_66 : location_info := LocationInfo file_0 62 18 62 27.
  Definition loc_67 : location_info := LocationInfo file_0 62 19 62 22.
  Definition loc_72 : location_info := LocationInfo file_0 91 2 91 16.
  Definition loc_73 : location_info := LocationInfo file_0 91 16 91 3.
  Definition loc_74 : location_info := LocationInfo file_0 92 2 92 35.
  Definition loc_75 : location_info := LocationInfo file_0 92 9 92 34.
  Definition loc_76 : location_info := LocationInfo file_0 92 9 92 31.
  Definition loc_77 : location_info := LocationInfo file_0 92 9 92 31.
  Definition loc_78 : location_info := LocationInfo file_0 92 32 92 33.
  Definition loc_79 : location_info := LocationInfo file_0 91 2 91 15.
  Definition loc_80 : location_info := LocationInfo file_0 91 3 91 15.
  Definition loc_81 : location_info := LocationInfo file_0 91 5 91 8.
  Definition loc_84 : location_info := LocationInfo file_0 102 2 102 20.
  Definition loc_85 : location_info := LocationInfo file_0 103 2 103 52.
  Definition loc_86 : location_info := LocationInfo file_0 104 2 104 31.
  Definition loc_87 : location_info := LocationInfo file_0 104 2 104 11.
  Definition loc_88 : location_info := LocationInfo file_0 104 3 104 6.
  Definition loc_89 : location_info := LocationInfo file_0 104 14 104 30.
  Definition loc_90 : location_info := LocationInfo file_0 104 26 104 30.
  Definition loc_91 : location_info := LocationInfo file_0 104 26 104 30.
  Definition loc_92 : location_info := LocationInfo file_0 103 2 103 11.
  Definition loc_93 : location_info := LocationInfo file_0 103 3 103 6.
  Definition loc_94 : location_info := LocationInfo file_0 103 14 103 51.
  Definition loc_95 : location_info := LocationInfo file_0 103 26 103 51.
  Definition loc_96 : location_info := LocationInfo file_0 103 27 103 43.
  Definition loc_97 : location_info := LocationInfo file_0 103 39 103 43.
  Definition loc_98 : location_info := LocationInfo file_0 103 39 103 43.
  Definition loc_99 : location_info := LocationInfo file_0 103 46 103 50.
  Definition loc_100 : location_info := LocationInfo file_0 103 46 103 50.
  Definition loc_101 : location_info := LocationInfo file_0 102 2 102 12.
  Definition loc_102 : location_info := LocationInfo file_0 102 3 102 6.
  Definition loc_103 : location_info := LocationInfo file_0 102 15 102 19.
  Definition loc_104 : location_info := LocationInfo file_0 102 15 102 19.

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
          LocInfoE loc_65 (use{it_layout size_t} (LocInfoE loc_66 ((LocInfoE loc_67 (global_mem)) at{struct_region} "cur"))) ;
        locinfo: loc_61 ;
        if: LocInfoE loc_61 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_61 ((UnOp (CastOp $ IntOp u32) (IntOp i32) (i2v 0 i32)) ={IntOp u32, IntOp u32} (LocInfoE loc_63 (use{it_layout u32} (LocInfoE loc_64 ("nr_pages")))))))
        then
        locinfo: loc_58 ;
          Goto "#5"
        else
        locinfo: loc_17 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_17 ;
        expr: (LocInfoE loc_55 (&(LocInfoE loc_56 ((LocInfoE loc_57 (global_mem)) at{struct_region} "base")))) ;
        locinfo: loc_19 ;
        LocInfoE loc_45 ((LocInfoE loc_46 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_47 ((LocInfoE loc_48 (use{it_layout size_t} (LocInfoE loc_49 ((LocInfoE loc_50 (global_mem)) at{struct_region} "cur")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_51 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_51 ((LocInfoE loc_52 (use{it_layout u32} (LocInfoE loc_53 ("nr_pages")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_54 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_54 (i2v 12 i32))))))))) ;
        locinfo: loc_38 ;
        if: LocInfoE loc_38 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_38 ((LocInfoE loc_39 (use{it_layout size_t} (LocInfoE loc_40 ((LocInfoE loc_41 (global_mem)) at{struct_region} "cur")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_42 (use{it_layout size_t} (LocInfoE loc_43 ((LocInfoE loc_44 (global_mem)) at{struct_region} "end")))))))
        then
        locinfo: loc_30 ;
          Goto "#3"
        else
        locinfo: loc_21 ;
          Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_21 ;
        Return (LocInfoE loc_22 (CopyAllocId (LocInfoE loc_26 (UnOp (CastOp $ PtrOp) (IntOp size_t) (LocInfoE loc_27 (use{it_layout size_t} (LocInfoE loc_28 ("ret")))))) (LocInfoE loc_23 (use{void*} (LocInfoE loc_24 ((LocInfoE loc_25 (global_mem)) at{struct_region} "base"))))))
      ]> $
      <[ "#3" :=
        locinfo: loc_30 ;
        LocInfoE loc_33 ((LocInfoE loc_34 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_35 (use{it_layout size_t} (LocInfoE loc_36 ("ret"))) ;
        locinfo: loc_31 ;
        Return (LocInfoE loc_32 (NULL))
      ]> $
      <[ "#4" :=
        locinfo: loc_21 ;
        Goto "#2"
      ]> $
      <[ "#5" :=
        locinfo: loc_58 ;
        Return (LocInfoE loc_59 (NULL))
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
        locinfo: loc_72 ;
        expr: (LocInfoE loc_79 (&(LocInfoE loc_80 ((LocInfoE loc_81 (global_mem)) at{struct_region} "base")))) ;
        locinfo: loc_74 ;
        Return (LocInfoE loc_75 (Call (LocInfoE loc_77 (global_hyp_early_alloc_contig)) [@{expr} LocInfoE loc_78 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_78 (i2v 1 i32))) ]))
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
        locinfo: loc_84 ;
        LocInfoE loc_101 ((LocInfoE loc_102 (global_mem)) at{struct_region} "base") <-{ void* }
          LocInfoE loc_103 (use{void*} (LocInfoE loc_104 ("virt"))) ;
        locinfo: loc_85 ;
        LocInfoE loc_92 ((LocInfoE loc_93 (global_mem)) at{struct_region} "end") <-{ it_layout size_t }
          LocInfoE loc_94 (UnOp (CastOp $ IntOp size_t) (IntOp size_t) (LocInfoE loc_95 ((LocInfoE loc_96 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_97 (use{void*} (LocInfoE loc_98 ("virt")))))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_99 (UnOp (CastOp $ IntOp size_t) (IntOp u32) (LocInfoE loc_99 (use{it_layout u32} (LocInfoE loc_100 ("size"))))))))) ;
        locinfo: loc_86 ;
        LocInfoE loc_87 ((LocInfoE loc_88 (global_mem)) at{struct_region} "cur") <-{ it_layout size_t }
          LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (PtrOp) (LocInfoE loc_90 (use{void*} (LocInfoE loc_91 ("virt"))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
