From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/early_alloc.c]. *)
Section code.
  Definition file_0 : string := "linux/early_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 20 1 20 27.
  Definition loc_3 : location_info := LocationInfo file_0 20 8 20 26.
  Definition loc_4 : location_info := LocationInfo file_0 20 8 20 20.
  Definition loc_5 : location_info := LocationInfo file_0 20 9 20 12.
  Definition loc_6 : location_info := LocationInfo file_0 20 9 20 12.
  Definition loc_7 : location_info := LocationInfo file_0 20 15 20 19.
  Definition loc_8 : location_info := LocationInfo file_0 20 15 20 19.
  Definition loc_9 : location_info := LocationInfo file_0 20 24 20 26.
  Definition loc_12 : location_info := LocationInfo file_0 30 1 30 25.
  Definition loc_13 : location_info := LocationInfo file_0 31 1 31 13.
  Definition loc_14 : location_info := LocationInfo file_0 32 1 35 2.
  Definition loc_15 : location_info := LocationInfo file_0 36 1 36 24.
  Definition loc_16 : location_info := LocationInfo file_0 37 1 37 20.
  Definition loc_17 : location_info := LocationInfo file_0 37 8 37 19.
  Definition loc_18 : location_info := LocationInfo file_0 37 16 37 19.
  Definition loc_19 : location_info := LocationInfo file_0 37 16 37 19.
  Definition loc_20 : location_info := LocationInfo file_0 36 1 36 11.
  Definition loc_21 : location_info := LocationInfo file_0 36 1 36 11.
  Definition loc_22 : location_info := LocationInfo file_0 36 12 36 22.
  Definition loc_23 : location_info := LocationInfo file_0 36 19 36 22.
  Definition loc_24 : location_info := LocationInfo file_0 36 19 36 22.
  Definition loc_25 : location_info := LocationInfo file_0 32 17 35 2.
  Definition loc_26 : location_info := LocationInfo file_0 33 2 33 12.
  Definition loc_27 : location_info := LocationInfo file_0 34 2 34 24.
  Definition loc_28 : location_info := LocationInfo file_0 34 9 34 23.
  Definition loc_29 : location_info := LocationInfo file_0 33 2 33 5.
  Definition loc_30 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_31 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_33 : location_info := LocationInfo file_0 32 5 32 15.
  Definition loc_34 : location_info := LocationInfo file_0 32 5 32 8.
  Definition loc_35 : location_info := LocationInfo file_0 32 5 32 8.
  Definition loc_36 : location_info := LocationInfo file_0 32 11 32 15.
  Definition loc_37 : location_info := LocationInfo file_0 32 11 32 15.
  Definition loc_38 : location_info := LocationInfo file_0 31 1 31 4.
  Definition loc_39 : location_info := LocationInfo file_0 31 1 31 12.
  Definition loc_40 : location_info := LocationInfo file_0 31 1 31 4.
  Definition loc_41 : location_info := LocationInfo file_0 31 1 31 4.
  Definition loc_42 : location_info := LocationInfo file_0 31 8 31 12.
  Definition loc_43 : location_info := LocationInfo file_0 30 21 30 24.
  Definition loc_44 : location_info := LocationInfo file_0 30 21 30 24.
  Definition loc_49 : location_info := LocationInfo file_0 42 1 42 13.
  Definition loc_50 : location_info := LocationInfo file_0 43 1 43 20.
  Definition loc_51 : location_info := LocationInfo file_0 44 1 44 12.
  Definition loc_52 : location_info := LocationInfo file_0 44 1 44 4.
  Definition loc_53 : location_info := LocationInfo file_0 44 7 44 11.
  Definition loc_54 : location_info := LocationInfo file_0 44 7 44 11.
  Definition loc_55 : location_info := LocationInfo file_0 43 1 43 5.
  Definition loc_56 : location_info := LocationInfo file_0 43 8 43 19.
  Definition loc_57 : location_info := LocationInfo file_0 43 8 43 12.
  Definition loc_58 : location_info := LocationInfo file_0 43 8 43 12.
  Definition loc_59 : location_info := LocationInfo file_0 43 15 43 19.
  Definition loc_60 : location_info := LocationInfo file_0 43 15 43 19.
  Definition loc_61 : location_info := LocationInfo file_0 42 1 42 5.
  Definition loc_62 : location_info := LocationInfo file_0 42 8 42 12.
  Definition loc_63 : location_info := LocationInfo file_0 42 8 42 12.
  Definition loc_66 : location_info := LocationInfo file_0 75 2 77 3.
  Definition loc_67 : location_info := LocationInfo file_0 79 1 79 27.
  Definition loc_68 : location_info := LocationInfo file_0 80 1 80 14.
  Definition loc_69 : location_info := LocationInfo file_0 81 1 81 15.
  Definition loc_70 : location_info := LocationInfo file_0 82 1 82 24.
  Definition loc_71 : location_info := LocationInfo file_0 83 1 83 20.
  Definition loc_72 : location_info := LocationInfo file_0 83 8 83 19.
  Definition loc_73 : location_info := LocationInfo file_0 83 16 83 19.
  Definition loc_74 : location_info := LocationInfo file_0 83 16 83 19.
  Definition loc_75 : location_info := LocationInfo file_0 82 1 82 11.
  Definition loc_76 : location_info := LocationInfo file_0 82 1 82 11.
  Definition loc_77 : location_info := LocationInfo file_0 82 12 82 22.
  Definition loc_78 : location_info := LocationInfo file_0 82 19 82 22.
  Definition loc_79 : location_info := LocationInfo file_0 82 19 82 22.
  Definition loc_80 : location_info := LocationInfo file_0 81 1 81 6.
  Definition loc_81 : location_info := LocationInfo file_0 81 1 81 14.
  Definition loc_82 : location_info := LocationInfo file_0 81 1 81 6.
  Definition loc_83 : location_info := LocationInfo file_0 81 1 81 6.
  Definition loc_84 : location_info := LocationInfo file_0 81 10 81 14.
  Definition loc_85 : location_info := LocationInfo file_0 80 1 80 5.
  Definition loc_86 : location_info := LocationInfo file_0 80 1 80 13.
  Definition loc_87 : location_info := LocationInfo file_0 80 1 80 5.
  Definition loc_88 : location_info := LocationInfo file_0 80 1 80 5.
  Definition loc_89 : location_info := LocationInfo file_0 80 9 80 13.
  Definition loc_90 : location_info := LocationInfo file_0 79 22 79 26.
  Definition loc_91 : location_info := LocationInfo file_0 79 22 79 26.
  Definition loc_94 : location_info := LocationInfo file_0 75 37 77 3.
  Definition loc_95 : location_info := LocationInfo file_0 76 4 76 26.
  Definition loc_96 : location_info := LocationInfo file_0 76 11 76 25.
  Definition loc_98 : location_info := LocationInfo file_0 75 6 75 35.
  Definition loc_99 : location_info := LocationInfo file_0 75 6 75 11.
  Definition loc_100 : location_info := LocationInfo file_0 75 6 75 11.
  Definition loc_101 : location_info := LocationInfo file_0 75 15 75 35.
  Definition loc_102 : location_info := LocationInfo file_0 75 31 75 35.
  Definition loc_105 : location_info := LocationInfo file_0 97 1 97 14.
  Definition loc_106 : location_info := LocationInfo file_0 98 1 98 14.
  Definition loc_107 : location_info := LocationInfo file_0 99 1 99 13.
  Definition loc_108 : location_info := LocationInfo file_0 99 1 99 5.
  Definition loc_109 : location_info := LocationInfo file_0 99 8 99 12.
  Definition loc_110 : location_info := LocationInfo file_0 99 8 99 12.
  Definition loc_111 : location_info := LocationInfo file_0 98 1 98 6.
  Definition loc_112 : location_info := LocationInfo file_0 98 9 98 13.
  Definition loc_113 : location_info := LocationInfo file_0 98 9 98 13.
  Definition loc_114 : location_info := LocationInfo file_0 97 1 97 6.
  Definition loc_115 : location_info := LocationInfo file_0 97 9 97 13.
  Definition loc_116 : location_info := LocationInfo file_0 97 9 97 13.

  (* Definition of function [hyp_early_alloc_nr_pages]. *)
  Definition impl_hyp_early_alloc_nr_pages (base cur : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 ((LocInfoE loc_4 ((LocInfoE loc_5 (use{it_layout u64} (LocInfoE loc_6 (cur)))) -{IntOp u64, IntOp u64} (LocInfoE loc_7 (use{it_layout u64} (LocInfoE loc_8 (base)))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_9 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_9 (i2v 12 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_page]. *)
  Definition impl_hyp_early_alloc_page (_end cur clear_page : loc): function := {|
    f_args := [
      ("arg", LPtr)
    ];
    f_local_vars := [
      ("ret", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ret" <-{ it_layout u64 }
          LocInfoE loc_43 (use{it_layout u64} (LocInfoE loc_44 (cur))) ;
        locinfo: loc_13 ;
        LocInfoE loc_38 (cur) <-{ it_layout u64 }
          LocInfoE loc_39 ((LocInfoE loc_40 (use{it_layout u64} (LocInfoE loc_41 (cur)))) +{IntOp u64, IntOp u64} (LocInfoE loc_42 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_42 (i2v 4096 i32))))) ;
        locinfo: loc_33 ;
        if: LocInfoE loc_33 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_33 ((LocInfoE loc_34 (use{it_layout u64} (LocInfoE loc_35 (cur)))) >{IntOp u64, IntOp u64} (LocInfoE loc_36 (use{it_layout u64} (LocInfoE loc_37 (_end)))))))
        then
        locinfo: loc_26 ;
          Goto "#2"
        else
        locinfo: loc_15 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_15 ;
        "_" <- LocInfoE loc_21 (clear_page) with
          [ LocInfoE loc_22 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_23 (use{it_layout u64} (LocInfoE loc_24 ("ret"))))) ] ;
        locinfo: loc_16 ;
        Return (LocInfoE loc_17 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_18 (use{it_layout u64} (LocInfoE loc_19 ("ret"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_26 ;
        LocInfoE loc_29 (cur) <-{ it_layout u64 }
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
  Definition impl_hyp_early_alloc_init (_end base cur : loc): function := {|
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
        LocInfoE loc_61 (base) <-{ it_layout u64 }
          LocInfoE loc_62 (use{it_layout u64} (LocInfoE loc_63 ("virt"))) ;
        locinfo: loc_50 ;
        LocInfoE loc_55 (_end) <-{ it_layout u64 }
          LocInfoE loc_56 ((LocInfoE loc_57 (use{it_layout u64} (LocInfoE loc_58 ("virt")))) +{IntOp u64, IntOp u64} (LocInfoE loc_59 (use{it_layout u64} (LocInfoE loc_60 ("size"))))) ;
        locinfo: loc_51 ;
        LocInfoE loc_52 (cur) <-{ it_layout u64 }
          LocInfoE loc_53 (use{it_layout u64} (LocInfoE loc_54 ("virt"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_early_alloc_page1]. *)
  Definition impl_hyp_early_alloc_page1 (cur1 size1 clear_page : loc): function := {|
    f_args := [
      ("arg", LPtr)
    ];
    f_local_vars := [
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_98 ;
        if: LocInfoE loc_98 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_98 ((LocInfoE loc_99 (use{it_layout u64} (LocInfoE loc_100 (size1)))) ≤{IntOp u64, IntOp u64} (LocInfoE loc_101 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_102 (i2v 4096 i32)))))))
        then
        locinfo: loc_95 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "ret" <-{ LPtr }
          LocInfoE loc_90 (use{LPtr} (LocInfoE loc_91 (cur1))) ;
        locinfo: loc_68 ;
        LocInfoE loc_85 (cur1) <-{ LPtr }
          LocInfoE loc_86 ((LocInfoE loc_87 (use{LPtr} (LocInfoE loc_88 (cur1)))) at_offset{it_layout u8, PtrOp, IntOp i32} (LocInfoE loc_89 (i2v 4096 i32))) ;
        locinfo: loc_69 ;
        LocInfoE loc_80 (size1) <-{ it_layout u64 }
          LocInfoE loc_81 ((LocInfoE loc_82 (use{it_layout u64} (LocInfoE loc_83 (size1)))) -{IntOp u64, IntOp u64} (LocInfoE loc_84 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_84 (i2v 4096 i32))))) ;
        locinfo: loc_70 ;
        "_" <- LocInfoE loc_76 (clear_page) with
          [ LocInfoE loc_77 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_78 (use{LPtr} (LocInfoE loc_79 ("ret"))))) ] ;
        locinfo: loc_71 ;
        Return (LocInfoE loc_72 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_73 (use{LPtr} (LocInfoE loc_74 ("ret"))))))
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
  Definition impl_hyp_early_alloc_init1 (base1 cur1 size1 : loc): function := {|
    f_args := [
      ("virt", LPtr);
      ("size", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_105 ;
        LocInfoE loc_114 (base1) <-{ LPtr }
          LocInfoE loc_115 (use{LPtr} (LocInfoE loc_116 ("virt"))) ;
        locinfo: loc_106 ;
        LocInfoE loc_111 (size1) <-{ it_layout u64 }
          LocInfoE loc_112 (use{it_layout u64} (LocInfoE loc_113 ("size"))) ;
        locinfo: loc_107 ;
        LocInfoE loc_108 (cur1) <-{ LPtr }
          LocInfoE loc_109 (use{LPtr} (LocInfoE loc_110 ("virt"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
