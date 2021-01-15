From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 19 1 19 27.
  Definition loc_3 : location_info := LocationInfo file_0 19 8 19 26.
  Definition loc_4 : location_info := LocationInfo file_0 19 8 19 20.
  Definition loc_5 : location_info := LocationInfo file_0 19 9 19 12.
  Definition loc_6 : location_info := LocationInfo file_0 19 9 19 12.
  Definition loc_7 : location_info := LocationInfo file_0 19 15 19 19.
  Definition loc_8 : location_info := LocationInfo file_0 19 15 19 19.
  Definition loc_9 : location_info := LocationInfo file_0 19 24 19 26.
  Definition loc_12 : location_info := LocationInfo file_0 29 1 29 25.
  Definition loc_13 : location_info := LocationInfo file_0 30 1 30 13.
  Definition loc_14 : location_info := LocationInfo file_0 31 1 34 2.
  Definition loc_15 : location_info := LocationInfo file_0 35 1 35 24.
  Definition loc_16 : location_info := LocationInfo file_0 36 1 36 20.
  Definition loc_17 : location_info := LocationInfo file_0 36 8 36 19.
  Definition loc_18 : location_info := LocationInfo file_0 36 16 36 19.
  Definition loc_19 : location_info := LocationInfo file_0 36 16 36 19.
  Definition loc_20 : location_info := LocationInfo file_0 35 1 35 11.
  Definition loc_21 : location_info := LocationInfo file_0 35 1 35 11.
  Definition loc_22 : location_info := LocationInfo file_0 35 12 35 22.
  Definition loc_23 : location_info := LocationInfo file_0 35 19 35 22.
  Definition loc_24 : location_info := LocationInfo file_0 35 19 35 22.
  Definition loc_25 : location_info := LocationInfo file_0 31 16 34 2.
  Definition loc_26 : location_info := LocationInfo file_0 32 2 32 12.
  Definition loc_27 : location_info := LocationInfo file_0 33 2 33 24.
  Definition loc_28 : location_info := LocationInfo file_0 33 9 33 23.
  Definition loc_29 : location_info := LocationInfo file_0 32 2 32 5.
  Definition loc_30 : location_info := LocationInfo file_0 32 8 32 11.
  Definition loc_31 : location_info := LocationInfo file_0 32 8 32 11.
  Definition loc_33 : location_info := LocationInfo file_0 31 5 31 14.
  Definition loc_34 : location_info := LocationInfo file_0 31 5 31 8.
  Definition loc_35 : location_info := LocationInfo file_0 31 5 31 8.
  Definition loc_36 : location_info := LocationInfo file_0 31 11 31 14.
  Definition loc_37 : location_info := LocationInfo file_0 31 11 31 14.
  Definition loc_38 : location_info := LocationInfo file_0 30 1 30 4.
  Definition loc_39 : location_info := LocationInfo file_0 30 1 30 12.
  Definition loc_40 : location_info := LocationInfo file_0 30 1 30 4.
  Definition loc_41 : location_info := LocationInfo file_0 30 1 30 4.
  Definition loc_42 : location_info := LocationInfo file_0 30 8 30 12.
  Definition loc_43 : location_info := LocationInfo file_0 29 21 29 24.
  Definition loc_44 : location_info := LocationInfo file_0 29 21 29 24.
  Definition loc_49 : location_info := LocationInfo file_0 41 1 41 13.
  Definition loc_50 : location_info := LocationInfo file_0 42 1 42 19.
  Definition loc_51 : location_info := LocationInfo file_0 43 1 43 12.
  Definition loc_52 : location_info := LocationInfo file_0 43 1 43 4.
  Definition loc_53 : location_info := LocationInfo file_0 43 7 43 11.
  Definition loc_54 : location_info := LocationInfo file_0 43 7 43 11.
  Definition loc_55 : location_info := LocationInfo file_0 42 1 42 4.
  Definition loc_56 : location_info := LocationInfo file_0 42 7 42 18.
  Definition loc_57 : location_info := LocationInfo file_0 42 7 42 11.
  Definition loc_58 : location_info := LocationInfo file_0 42 7 42 11.
  Definition loc_59 : location_info := LocationInfo file_0 42 14 42 18.
  Definition loc_60 : location_info := LocationInfo file_0 42 14 42 18.
  Definition loc_61 : location_info := LocationInfo file_0 41 1 41 5.
  Definition loc_62 : location_info := LocationInfo file_0 41 8 41 12.
  Definition loc_63 : location_info := LocationInfo file_0 41 8 41 12.
  Definition loc_66 : location_info := LocationInfo file_0 74 1 76 2.
  Definition loc_67 : location_info := LocationInfo file_0 78 1 78 27.
  Definition loc_68 : location_info := LocationInfo file_0 79 1 79 14.
  Definition loc_69 : location_info := LocationInfo file_0 80 1 80 15.
  Definition loc_70 : location_info := LocationInfo file_0 81 1 81 24.
  Definition loc_71 : location_info := LocationInfo file_0 82 1 82 20.
  Definition loc_72 : location_info := LocationInfo file_0 82 8 82 19.
  Definition loc_73 : location_info := LocationInfo file_0 82 16 82 19.
  Definition loc_74 : location_info := LocationInfo file_0 82 16 82 19.
  Definition loc_75 : location_info := LocationInfo file_0 81 1 81 11.
  Definition loc_76 : location_info := LocationInfo file_0 81 1 81 11.
  Definition loc_77 : location_info := LocationInfo file_0 81 12 81 22.
  Definition loc_78 : location_info := LocationInfo file_0 81 19 81 22.
  Definition loc_79 : location_info := LocationInfo file_0 81 19 81 22.
  Definition loc_80 : location_info := LocationInfo file_0 80 1 80 6.
  Definition loc_81 : location_info := LocationInfo file_0 80 1 80 14.
  Definition loc_82 : location_info := LocationInfo file_0 80 1 80 6.
  Definition loc_83 : location_info := LocationInfo file_0 80 1 80 6.
  Definition loc_84 : location_info := LocationInfo file_0 80 10 80 14.
  Definition loc_85 : location_info := LocationInfo file_0 79 1 79 5.
  Definition loc_86 : location_info := LocationInfo file_0 79 1 79 13.
  Definition loc_87 : location_info := LocationInfo file_0 79 1 79 5.
  Definition loc_88 : location_info := LocationInfo file_0 79 1 79 5.
  Definition loc_89 : location_info := LocationInfo file_0 79 9 79 13.
  Definition loc_90 : location_info := LocationInfo file_0 78 22 78 26.
  Definition loc_91 : location_info := LocationInfo file_0 78 22 78 26.
  Definition loc_94 : location_info := LocationInfo file_0 74 36 76 2.
  Definition loc_95 : location_info := LocationInfo file_0 75 2 75 24.
  Definition loc_96 : location_info := LocationInfo file_0 75 9 75 23.
  Definition loc_98 : location_info := LocationInfo file_0 74 5 74 34.
  Definition loc_99 : location_info := LocationInfo file_0 74 5 74 10.
  Definition loc_100 : location_info := LocationInfo file_0 74 5 74 10.
  Definition loc_101 : location_info := LocationInfo file_0 74 14 74 34.
  Definition loc_102 : location_info := LocationInfo file_0 74 30 74 34.
  Definition loc_105 : location_info := LocationInfo file_0 96 1 96 14.
  Definition loc_106 : location_info := LocationInfo file_0 97 1 97 14.
  Definition loc_107 : location_info := LocationInfo file_0 98 1 98 13.
  Definition loc_108 : location_info := LocationInfo file_0 98 1 98 5.
  Definition loc_109 : location_info := LocationInfo file_0 98 8 98 12.
  Definition loc_110 : location_info := LocationInfo file_0 98 8 98 12.
  Definition loc_111 : location_info := LocationInfo file_0 97 1 97 6.
  Definition loc_112 : location_info := LocationInfo file_0 97 9 97 13.
  Definition loc_113 : location_info := LocationInfo file_0 97 9 97 13.
  Definition loc_114 : location_info := LocationInfo file_0 96 1 96 6.
  Definition loc_115 : location_info := LocationInfo file_0 96 9 96 13.
  Definition loc_116 : location_info := LocationInfo file_0 96 9 96 13.

  (* Definition of function [hyp_early_alloc_nr_pages]. *)
  Definition impl_hyp_early_alloc_nr_pages (global_base global_cur : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 ((LocInfoE loc_4 ((LocInfoE loc_5 (use{it_layout u64} (LocInfoE loc_6 (global_cur)))) -{IntOp u64, IntOp u64} (LocInfoE loc_7 (use{it_layout u64} (LocInfoE loc_8 (global_base)))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_9 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_9 (i2v 12 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_page]. *)
  Definition impl_hyp_early_alloc_page (global_cur global_end global_clear_page : loc): function := {|
    f_args := [
      ("arg", void*)
    ];
    f_local_vars := [
      ("ret", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ it_layout u64 }
          LocInfoE loc_43 (use{it_layout u64} (LocInfoE loc_44 (global_cur))) ;
        locinfo: loc_13 ;
        LocInfoE loc_38 (global_cur) <-{ it_layout u64 }
          LocInfoE loc_39 ((LocInfoE loc_40 (use{it_layout u64} (LocInfoE loc_41 (global_cur)))) +{IntOp u64, IntOp u64} (LocInfoE loc_42 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_42 (i2v 4096 i32))))) ;
        locinfo: loc_33 ;
        if: LocInfoE loc_33 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_33 ((LocInfoE loc_34 (use{it_layout u64} (LocInfoE loc_35 (global_cur)))) >{IntOp u64, IntOp u64} (LocInfoE loc_36 (use{it_layout u64} (LocInfoE loc_37 (global_end)))))))
        then
        locinfo: loc_26 ;
          Goto "#2"
        else
        locinfo: loc_15 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_15 ;
        "_" <- LocInfoE loc_21 (global_clear_page) with
          [ LocInfoE loc_22 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_23 (use{it_layout u64} (LocInfoE loc_24 ("ret"))))) ] ;
        locinfo: loc_16 ;
        Return (LocInfoE loc_17 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_18 (use{it_layout u64} (LocInfoE loc_19 ("ret"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_26 ;
        LocInfoE loc_29 (global_cur) <-{ it_layout u64 }
          LocInfoE loc_30 (use{it_layout u64} (LocInfoE loc_31 ("ret"))) ;
        locinfo: loc_27 ;
        Return (LocInfoE loc_28 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_15 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_init]. *)
  Definition impl_hyp_early_alloc_init (global_base global_cur global_end : loc): function := {|
    f_args := [
      ("virt", it_layout u64);
      ("size", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_49 ;
        LocInfoE loc_61 (global_base) <-{ it_layout u64 }
          LocInfoE loc_62 (use{it_layout u64} (LocInfoE loc_63 ("virt"))) ;
        locinfo: loc_50 ;
        LocInfoE loc_55 (global_end) <-{ it_layout u64 }
          LocInfoE loc_56 ((LocInfoE loc_57 (use{it_layout u64} (LocInfoE loc_58 ("virt")))) +{IntOp u64, IntOp u64} (LocInfoE loc_59 (use{it_layout u64} (LocInfoE loc_60 ("size"))))) ;
        locinfo: loc_51 ;
        LocInfoE loc_52 (global_cur) <-{ it_layout u64 }
          LocInfoE loc_53 (use{it_layout u64} (LocInfoE loc_54 ("virt"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_page1]. *)
  Definition impl_hyp_early_alloc_page1 (global_cur1 global_size1 global_clear_page : loc): function := {|
    f_args := [
      ("arg", void*)
    ];
    f_local_vars := [
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_98 ;
        if: LocInfoE loc_98 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_98 ((LocInfoE loc_99 (use{it_layout u64} (LocInfoE loc_100 (global_size1)))) ≤{IntOp u64, IntOp u64} (LocInfoE loc_101 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_102 (i2v 4096 i32)))))))
        then
        locinfo: loc_95 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "ret" <-{ void* }
          LocInfoE loc_90 (use{void*} (LocInfoE loc_91 (global_cur1))) ;
        locinfo: loc_68 ;
        LocInfoE loc_85 (global_cur1) <-{ void* }
          LocInfoE loc_86 ((LocInfoE loc_87 (use{void*} (LocInfoE loc_88 (global_cur1)))) at_offset{it_layout u8, PtrOp, IntOp i32} (LocInfoE loc_89 (i2v 4096 i32))) ;
        locinfo: loc_69 ;
        LocInfoE loc_80 (global_size1) <-{ it_layout u64 }
          LocInfoE loc_81 ((LocInfoE loc_82 (use{it_layout u64} (LocInfoE loc_83 (global_size1)))) -{IntOp u64, IntOp u64} (LocInfoE loc_84 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_84 (i2v 4096 i32))))) ;
        locinfo: loc_70 ;
        "_" <- LocInfoE loc_76 (global_clear_page) with
          [ LocInfoE loc_77 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_78 (use{void*} (LocInfoE loc_79 ("ret"))))) ] ;
        locinfo: loc_71 ;
        Return (LocInfoE loc_72 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_73 (use{void*} (LocInfoE loc_74 ("ret"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_95 ;
        Return (LocInfoE loc_96 (NULL))
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_init1]. *)
  Definition impl_hyp_early_alloc_init1 (global_base1 global_cur1 global_size1 : loc): function := {|
    f_args := [
      ("virt", void*);
      ("size", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_105 ;
        LocInfoE loc_114 (global_base1) <-{ void* }
          LocInfoE loc_115 (use{void*} (LocInfoE loc_116 ("virt"))) ;
        locinfo: loc_106 ;
        LocInfoE loc_111 (global_size1) <-{ it_layout u64 }
          LocInfoE loc_112 (use{it_layout u64} (LocInfoE loc_113 ("size"))) ;
        locinfo: loc_107 ;
        LocInfoE loc_108 (global_cur1) <-{ void* }
          LocInfoE loc_109 (use{void*} (LocInfoE loc_110 ("virt"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
