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
  Definition loc_12 : location_info := LocationInfo file_0 31 1 31 25.
  Definition loc_13 : location_info := LocationInfo file_0 32 1 32 13.
  Definition loc_14 : location_info := LocationInfo file_0 33 1 36 2.
  Definition loc_15 : location_info := LocationInfo file_0 37 1 37 24.
  Definition loc_16 : location_info := LocationInfo file_0 38 1 38 20.
  Definition loc_17 : location_info := LocationInfo file_0 38 8 38 19.
  Definition loc_18 : location_info := LocationInfo file_0 38 16 38 19.
  Definition loc_19 : location_info := LocationInfo file_0 38 16 38 19.
  Definition loc_20 : location_info := LocationInfo file_0 37 1 37 11.
  Definition loc_21 : location_info := LocationInfo file_0 37 1 37 11.
  Definition loc_22 : location_info := LocationInfo file_0 37 12 37 22.
  Definition loc_23 : location_info := LocationInfo file_0 37 19 37 22.
  Definition loc_24 : location_info := LocationInfo file_0 37 19 37 22.
  Definition loc_25 : location_info := LocationInfo file_0 33 17 36 2.
  Definition loc_26 : location_info := LocationInfo file_0 34 2 34 12.
  Definition loc_27 : location_info := LocationInfo file_0 35 2 35 24.
  Definition loc_28 : location_info := LocationInfo file_0 35 9 35 23.
  Definition loc_29 : location_info := LocationInfo file_0 34 2 34 5.
  Definition loc_30 : location_info := LocationInfo file_0 34 8 34 11.
  Definition loc_31 : location_info := LocationInfo file_0 34 8 34 11.
  Definition loc_33 : location_info := LocationInfo file_0 33 5 33 15.
  Definition loc_34 : location_info := LocationInfo file_0 33 5 33 8.
  Definition loc_35 : location_info := LocationInfo file_0 33 5 33 8.
  Definition loc_36 : location_info := LocationInfo file_0 33 11 33 15.
  Definition loc_37 : location_info := LocationInfo file_0 33 11 33 15.
  Definition loc_38 : location_info := LocationInfo file_0 32 1 32 4.
  Definition loc_39 : location_info := LocationInfo file_0 32 1 32 12.
  Definition loc_40 : location_info := LocationInfo file_0 32 1 32 4.
  Definition loc_41 : location_info := LocationInfo file_0 32 1 32 4.
  Definition loc_42 : location_info := LocationInfo file_0 32 8 32 12.
  Definition loc_43 : location_info := LocationInfo file_0 31 21 31 24.
  Definition loc_44 : location_info := LocationInfo file_0 31 21 31 24.
  Definition loc_49 : location_info := LocationInfo file_0 43 1 43 13.
  Definition loc_50 : location_info := LocationInfo file_0 44 1 44 20.
  Definition loc_51 : location_info := LocationInfo file_0 45 1 45 12.
  Definition loc_52 : location_info := LocationInfo file_0 45 1 45 4.
  Definition loc_53 : location_info := LocationInfo file_0 45 7 45 11.
  Definition loc_54 : location_info := LocationInfo file_0 45 7 45 11.
  Definition loc_55 : location_info := LocationInfo file_0 44 1 44 5.
  Definition loc_56 : location_info := LocationInfo file_0 44 8 44 19.
  Definition loc_57 : location_info := LocationInfo file_0 44 8 44 12.
  Definition loc_58 : location_info := LocationInfo file_0 44 8 44 12.
  Definition loc_59 : location_info := LocationInfo file_0 44 15 44 19.
  Definition loc_60 : location_info := LocationInfo file_0 44 15 44 19.
  Definition loc_61 : location_info := LocationInfo file_0 43 1 43 5.
  Definition loc_62 : location_info := LocationInfo file_0 43 8 43 12.
  Definition loc_63 : location_info := LocationInfo file_0 43 8 43 12.
  Definition loc_66 : location_info := LocationInfo file_0 76 2 78 3.
  Definition loc_67 : location_info := LocationInfo file_0 80 1 80 27.
  Definition loc_68 : location_info := LocationInfo file_0 81 1 81 14.
  Definition loc_69 : location_info := LocationInfo file_0 82 1 82 15.
  Definition loc_70 : location_info := LocationInfo file_0 83 1 83 24.
  Definition loc_71 : location_info := LocationInfo file_0 84 1 84 20.
  Definition loc_72 : location_info := LocationInfo file_0 84 8 84 19.
  Definition loc_73 : location_info := LocationInfo file_0 84 16 84 19.
  Definition loc_74 : location_info := LocationInfo file_0 84 16 84 19.
  Definition loc_75 : location_info := LocationInfo file_0 83 1 83 11.
  Definition loc_76 : location_info := LocationInfo file_0 83 1 83 11.
  Definition loc_77 : location_info := LocationInfo file_0 83 12 83 22.
  Definition loc_78 : location_info := LocationInfo file_0 83 19 83 22.
  Definition loc_79 : location_info := LocationInfo file_0 83 19 83 22.
  Definition loc_80 : location_info := LocationInfo file_0 82 1 82 6.
  Definition loc_81 : location_info := LocationInfo file_0 82 1 82 14.
  Definition loc_82 : location_info := LocationInfo file_0 82 1 82 6.
  Definition loc_83 : location_info := LocationInfo file_0 82 1 82 6.
  Definition loc_84 : location_info := LocationInfo file_0 82 10 82 14.
  Definition loc_85 : location_info := LocationInfo file_0 81 1 81 5.
  Definition loc_86 : location_info := LocationInfo file_0 81 1 81 13.
  Definition loc_87 : location_info := LocationInfo file_0 81 1 81 5.
  Definition loc_88 : location_info := LocationInfo file_0 81 1 81 5.
  Definition loc_89 : location_info := LocationInfo file_0 81 9 81 13.
  Definition loc_90 : location_info := LocationInfo file_0 80 22 80 26.
  Definition loc_91 : location_info := LocationInfo file_0 80 22 80 26.
  Definition loc_94 : location_info := LocationInfo file_0 76 37 78 3.
  Definition loc_95 : location_info := LocationInfo file_0 77 4 77 26.
  Definition loc_96 : location_info := LocationInfo file_0 77 11 77 25.
  Definition loc_98 : location_info := LocationInfo file_0 76 6 76 35.
  Definition loc_99 : location_info := LocationInfo file_0 76 6 76 11.
  Definition loc_100 : location_info := LocationInfo file_0 76 6 76 11.
  Definition loc_101 : location_info := LocationInfo file_0 76 15 76 35.
  Definition loc_102 : location_info := LocationInfo file_0 76 31 76 35.
  Definition loc_105 : location_info := LocationInfo file_0 89 1 89 14.
  Definition loc_106 : location_info := LocationInfo file_0 90 1 90 14.
  Definition loc_107 : location_info := LocationInfo file_0 91 1 91 13.
  Definition loc_108 : location_info := LocationInfo file_0 91 1 91 5.
  Definition loc_109 : location_info := LocationInfo file_0 91 8 91 12.
  Definition loc_110 : location_info := LocationInfo file_0 91 8 91 12.
  Definition loc_111 : location_info := LocationInfo file_0 90 1 90 6.
  Definition loc_112 : location_info := LocationInfo file_0 90 9 90 13.
  Definition loc_113 : location_info := LocationInfo file_0 90 9 90 13.
  Definition loc_114 : location_info := LocationInfo file_0 89 1 89 6.
  Definition loc_115 : location_info := LocationInfo file_0 89 9 89 13.
  Definition loc_116 : location_info := LocationInfo file_0 89 9 89 13.

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
