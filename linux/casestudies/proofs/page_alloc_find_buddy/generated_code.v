From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc_find_buddy.c]. *)
Section code.
  Definition file_0 : string := "linux/casestudies/page_alloc_find_buddy.c".
  Definition loc_2 : location_info := LocationInfo file_0 59 1 59 62.
  Definition loc_3 : location_info := LocationInfo file_0 59 8 59 61.
  Definition loc_4 : location_info := LocationInfo file_0 59 17 59 60.
  Definition loc_5 : location_info := LocationInfo file_0 59 18 59 37.
  Definition loc_6 : location_info := LocationInfo file_0 59 31 59 37.
  Definition loc_7 : location_info := LocationInfo file_0 59 31 59 37.
  Definition loc_8 : location_info := LocationInfo file_0 59 40 59 59.
  Definition loc_9 : location_info := LocationInfo file_0 59 40 59 59.
  Definition loc_12 : location_info := LocationInfo file_0 64 1 64 52.
  Definition loc_13 : location_info := LocationInfo file_0 64 8 64 51.
  Definition loc_14 : location_info := LocationInfo file_0 64 9 64 28.
  Definition loc_15 : location_info := LocationInfo file_0 64 22 64 28.
  Definition loc_16 : location_info := LocationInfo file_0 64 22 64 28.
  Definition loc_17 : location_info := LocationInfo file_0 64 31 64 50.
  Definition loc_18 : location_info := LocationInfo file_0 64 31 64 50.
  Definition loc_21 : location_info := LocationInfo file_0 171 1 171 22.
  Definition loc_22 : location_info := LocationInfo file_0 171 22 171 2.
  Definition loc_23 : location_info := LocationInfo file_0 172 1 172 109.
  Definition loc_24 : location_info := LocationInfo file_0 174 1 174 25.
  Definition loc_25 : location_info := LocationInfo file_0 175 1 176 24.
  Definition loc_26 : location_info := LocationInfo file_0 178 1 178 62.
  Definition loc_27 : location_info := LocationInfo file_0 178 8 178 61.
  Definition loc_28 : location_info := LocationInfo file_0 178 9 178 43.
  Definition loc_29 : location_info := LocationInfo file_0 178 29 178 42.
  Definition loc_30 : location_info := LocationInfo file_0 178 29 178 42.
  Definition loc_31 : location_info := LocationInfo file_0 178 46 178 60.
  Definition loc_32 : location_info := LocationInfo file_0 178 47 178 53.
  Definition loc_33 : location_info := LocationInfo file_0 178 47 178 53.
  Definition loc_34 : location_info := LocationInfo file_0 178 57 178 59.
  Definition loc_35 : location_info := LocationInfo file_0 176 2 176 24.
  Definition loc_36 : location_info := LocationInfo file_0 176 9 176 23.
  Definition loc_39 : location_info := LocationInfo file_0 175 5 175 29.
  Definition loc_40 : location_info := LocationInfo file_0 175 5 175 9.
  Definition loc_41 : location_info := LocationInfo file_0 175 5 175 9.
  Definition loc_42 : location_info := LocationInfo file_0 175 12 175 29.
  Definition loc_43 : location_info := LocationInfo file_0 175 12 175 29.
  Definition loc_44 : location_info := LocationInfo file_0 175 12 175 16.
  Definition loc_45 : location_info := LocationInfo file_0 175 12 175 16.
  Definition loc_46 : location_info := LocationInfo file_0 175 33 175 56.
  Definition loc_47 : location_info := LocationInfo file_0 175 33 175 37.
  Definition loc_48 : location_info := LocationInfo file_0 175 33 175 37.
  Definition loc_49 : location_info := LocationInfo file_0 175 41 175 56.
  Definition loc_50 : location_info := LocationInfo file_0 175 41 175 56.
  Definition loc_51 : location_info := LocationInfo file_0 175 41 175 45.
  Definition loc_52 : location_info := LocationInfo file_0 175 41 175 45.
  Definition loc_53 : location_info := LocationInfo file_0 174 1 174 5.
  Definition loc_54 : location_info := LocationInfo file_0 174 1 174 24.
  Definition loc_55 : location_info := LocationInfo file_0 174 1 174 5.
  Definition loc_56 : location_info := LocationInfo file_0 174 1 174 5.
  Definition loc_57 : location_info := LocationInfo file_0 174 9 174 24.
  Definition loc_58 : location_info := LocationInfo file_0 174 10 174 14.
  Definition loc_59 : location_info := LocationInfo file_0 174 18 174 23.
  Definition loc_60 : location_info := LocationInfo file_0 174 18 174 23.
  Definition loc_61 : location_info := LocationInfo file_0 172 20 172 108.
  Definition loc_62 : location_info := LocationInfo file_0 172 34 172 107.
  Definition loc_63 : location_info := LocationInfo file_0 172 35 172 100.
  Definition loc_64 : location_info := LocationInfo file_0 172 38 172 60.
  Definition loc_65 : location_info := LocationInfo file_0 172 57 172 60.
  Definition loc_66 : location_info := LocationInfo file_0 172 57 172 60.
  Definition loc_67 : location_info := LocationInfo file_0 172 63 172 97.
  Definition loc_68 : location_info := LocationInfo file_0 172 83 172 96.
  Definition loc_69 : location_info := LocationInfo file_0 172 83 172 96.
  Definition loc_70 : location_info := LocationInfo file_0 172 104 172 106.
  Definition loc_73 : location_info := LocationInfo file_0 171 1 171 21.
  Definition loc_74 : location_info := LocationInfo file_0 171 2 171 21.
  Definition loc_75 : location_info := LocationInfo file_0 171 3 171 7.
  Definition loc_76 : location_info := LocationInfo file_0 171 3 171 7.

  (* Definition of struct [hyp_page]. *)
  Program Definition struct_hyp_page := {|
    sl_members := [
      (Some "refcount", it_layout u16);
      (Some "order", it_layout u16)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [hyp_pool]. *)
  Program Definition struct_hyp_pool := {|
    sl_members := [
      (Some "range_start", it_layout u64);
      (Some "range_end", it_layout u64);
      (Some "max_order", it_layout u16);
      (None, Layout 6%nat 0%nat)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [hyp_phys_to_virt]. *)
  Definition impl_hyp_phys_to_virt (global_hyp_physvirt_offset : loc): function := {|
    f_args := [
      ("phys", it_layout u64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_4 ((LocInfoE loc_5 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_6 (use{it_layout u64} (LocInfoE loc_7 ("phys")))))) -{IntOp u64, IntOp u64} (LocInfoE loc_8 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_8 (use{it_layout i64} (LocInfoE loc_9 (global_hyp_physvirt_offset))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_virt_to_phys]. *)
  Definition impl_hyp_virt_to_phys (global_hyp_physvirt_offset : loc): function := {|
    f_args := [
      ("addr", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 ((LocInfoE loc_14 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_15 (use{void*} (LocInfoE loc_16 ("addr")))))) +{IntOp u64, IntOp u64} (LocInfoE loc_17 (UnOp (CastOp $ IntOp u64) (IntOp i64) (LocInfoE loc_17 (use{it_layout i64} (LocInfoE loc_18 (global_hyp_physvirt_offset))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [__find_buddy]. *)
  Definition impl___find_buddy (global___hyp_vmemmap : loc): function := {|
    f_args := [
      ("pool", void*);
      ("p", void*);
      ("order", it_layout u32)
    ];
    f_local_vars := [
      ("addr", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_21 ;
        expr: (LocInfoE loc_73 (&(LocInfoE loc_74 ((LocInfoE loc_75 (!{void*} (LocInfoE loc_76 ("pool")))) at{struct_hyp_pool} "range_start")))) ;
        "addr" <-{ it_layout u64 }
          LocInfoE loc_61 (UnOp (CastOp $ IntOp u64) (IntOp ptrdiff_t) (LocInfoE loc_62 ((LocInfoE loc_63 ((LocInfoE loc_64 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_65 (use{void*} (LocInfoE loc_66 ("p")))))) sub_ptr{layout_of struct_hyp_page, PtrOp, PtrOp} (LocInfoE loc_67 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_68 (use{it_layout u64} (LocInfoE loc_69 (global___hyp_vmemmap)))))))) <<{IntOp ptrdiff_t, IntOp ptrdiff_t} (LocInfoE loc_70 (UnOp (CastOp $ IntOp ptrdiff_t) (IntOp i32) (LocInfoE loc_70 (i2v 12 i32))))))) ;
        locinfo: loc_24 ;
        LocInfoE loc_53 ("addr") <-{ it_layout u64 }
          LocInfoE loc_54 ((LocInfoE loc_55 (use{it_layout u64} (LocInfoE loc_56 ("addr")))) ^{IntOp u64, IntOp u64} (LocInfoE loc_57 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_57 ((LocInfoE loc_58 (i2v 4096 i32)) <<{IntOp i32, IntOp i32} (LocInfoE loc_59 (UnOp (CastOp $ IntOp i32) (IntOp u32) (LocInfoE loc_59 (use{it_layout u32} (LocInfoE loc_60 ("order"))))))))))) ;
        locinfo: loc_39 ;
        if: LocInfoE loc_39 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_39 ((LocInfoE loc_40 (use{it_layout u64} (LocInfoE loc_41 ("addr")))) <{IntOp u64, IntOp u64} (LocInfoE loc_42 (use{it_layout u64} (LocInfoE loc_43 ((LocInfoE loc_44 (!{void*} (LocInfoE loc_45 ("pool")))) at{struct_hyp_pool} "range_start")))))))
        then
        locinfo: loc_35 ;
          Goto "#2"
        else
        Goto "#4"
      ]> $
      <[ "#1" :=
        locinfo: loc_26 ;
        Return (LocInfoE loc_27 ((LocInfoE loc_28 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_29 (use{it_layout u64} (LocInfoE loc_30 (global___hyp_vmemmap)))))) at_offset{layout_of struct_hyp_page, PtrOp, IntOp u64} (LocInfoE loc_31 ((LocInfoE loc_32 (use{it_layout u64} (LocInfoE loc_33 ("addr")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_34 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_34 (i2v 12 i32))))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_35 ;
        Return (LocInfoE loc_36 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_26 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_46 ;
        if: LocInfoE loc_46 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_46 ((LocInfoE loc_47 (use{it_layout u64} (LocInfoE loc_48 ("addr")))) ≥{IntOp u64, IntOp u64} (LocInfoE loc_49 (use{it_layout u64} (LocInfoE loc_50 ((LocInfoE loc_51 (!{void*} (LocInfoE loc_52 ("pool")))) at{struct_hyp_pool} "range_end")))))))
        then
        locinfo: loc_35 ;
          Goto "#2"
        else
        locinfo: loc_26 ;
          Goto "#3"
      ]> $∅
    )%E
  |}.
End code.
