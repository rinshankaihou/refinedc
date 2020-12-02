From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.wrapping_add Require Import wrapping_def.
Set Default Proof Using "Type".

(* Generated from [examples/wrapping_add.c]. *)
Section code.
  Definition file_0 : string := "examples/wrapping_add.c".
  Definition loc_2 : location_info := LocationInfo file_0 16 2 16 144.
  Definition loc_3 : location_info := LocationInfo file_0 16 9 16 143.
  Definition loc_4 : location_info := LocationInfo file_0 16 95 16 102.
  Definition loc_5 : location_info := LocationInfo file_0 16 96 16 97.
  Definition loc_6 : location_info := LocationInfo file_0 16 96 16 97.
  Definition loc_7 : location_info := LocationInfo file_0 16 100 16 101.
  Definition loc_8 : location_info := LocationInfo file_0 16 100 16 101.
  Definition loc_9 : location_info := LocationInfo file_0 16 84 16 85.
  Definition loc_10 : location_info := LocationInfo file_0 16 84 16 85.
  Definition loc_11 : location_info := LocationInfo file_0 16 125 16 142.
  Definition loc_12 : location_info := LocationInfo file_0 16 126 16 129.
  Definition loc_13 : location_info := LocationInfo file_0 16 126 16 129.
  Definition loc_14 : location_info := LocationInfo file_0 16 132 16 141.
  Definition loc_15 : location_info := LocationInfo file_0 16 134 16 135.
  Definition loc_16 : location_info := LocationInfo file_0 16 134 16 135.
  Definition loc_17 : location_info := LocationInfo file_0 16 138 16 139.
  Definition loc_18 : location_info := LocationInfo file_0 16 138 16 139.

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
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (CheckedMacroE (WrappingAdd size_t size_t) [
                                  (LocInfoE loc_9 (use{it_layout size_t} (LocInfoE loc_10 ("a"))) : expr) ;
                                  (LocInfoE loc_4 ((LocInfoE loc_5 (use{it_layout size_t} (LocInfoE loc_6 ("b")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_7 (use{it_layout size_t} (LocInfoE loc_8 ("c"))))) : expr)
                                ] (LocInfoE loc_11 ((LocInfoE loc_12 (use{it_layout size_t} (LocInfoE loc_13 ("a")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_14 ((LocInfoE loc_15 (use{it_layout size_t} (LocInfoE loc_16 ("b")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_17 (use{it_layout size_t} (LocInfoE loc_18 ("c"))))))) : expr)))
      ]> $∅
    )%E
  |}.
End code.
