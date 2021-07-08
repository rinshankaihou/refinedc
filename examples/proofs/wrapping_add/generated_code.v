From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.wrapping_add Require Import wrapping_def.
Set Default Proof Using "Type".

(* Generated from [examples/wrapping_add.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/wrapping_add.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 16 2 16 144.
  Definition loc_12 : location_info := LocationInfo file_1 16 9 16 143.
  Definition loc_13 : location_info := LocationInfo file_1 16 95 16 102.
  Definition loc_14 : location_info := LocationInfo file_1 16 96 16 97.
  Definition loc_15 : location_info := LocationInfo file_1 16 96 16 97.
  Definition loc_16 : location_info := LocationInfo file_1 16 100 16 101.
  Definition loc_17 : location_info := LocationInfo file_1 16 100 16 101.
  Definition loc_18 : location_info := LocationInfo file_1 16 84 16 85.
  Definition loc_19 : location_info := LocationInfo file_1 16 84 16 85.
  Definition loc_20 : location_info := LocationInfo file_1 16 125 16 142.
  Definition loc_21 : location_info := LocationInfo file_1 16 126 16 129.
  Definition loc_22 : location_info := LocationInfo file_1 16 126 16 129.
  Definition loc_23 : location_info := LocationInfo file_1 16 132 16 141.
  Definition loc_24 : location_info := LocationInfo file_1 16 134 16 135.
  Definition loc_25 : location_info := LocationInfo file_1 16 134 16 135.
  Definition loc_26 : location_info := LocationInfo file_1 16 138 16 139.
  Definition loc_27 : location_info := LocationInfo file_1 16 138 16 139.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [wrapping_add]. *)
  Definition impl_wrapping_add : function := {|
    f_args := [
      ("a", it_layout size_t);
      ("b", it_layout size_t);
      ("c", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (LocInfoE loc_12 (CheckedMacroE (WrappingAdd size_t size_t) [
                                   (LocInfoE loc_18 (use{it_layout size_t} (LocInfoE loc_19 ("a"))) : expr) ;
                                   (LocInfoE loc_13 ((LocInfoE loc_14 (use{it_layout size_t} (LocInfoE loc_15 ("b")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_16 (use{it_layout size_t} (LocInfoE loc_17 ("c"))))) : expr)
                                 ] (LocInfoE loc_20 ((LocInfoE loc_21 (use{it_layout size_t} (LocInfoE loc_22 ("a")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_23 ((LocInfoE loc_24 (use{it_layout size_t} (LocInfoE loc_25 ("b")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_26 (use{it_layout size_t} (LocInfoE loc_27 ("c"))))))) : expr)))
      ]> $∅
    )%E
  |}.
End code.
