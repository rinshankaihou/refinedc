#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <refinedc.h>

//@rc::import t07_arrays_extra from refinedc.tutorial.t07_arrays

[[rc::parameters("ar : loc", "elts : {list Z}", "i : nat", "j : nat", "v1: Z", "v2: Z")]]
[[rc::args("ar @&own<array<i32, {elts `at_type` (int i32)}>>")]]
[[rc::args("i @ int<i32>", "j @ int<i32>")]]
[[rc::requires("{elts !! i = Some v1}", "{elts !! j = Some v2}", "{i ≠ j}")]]
[[rc::ensures("ar @&own<array<i32, {<[j:=v1]>(<[i:=v2]>elts) `at_type` (int i32)}>>")]]
void permute(int* ar, int i, int j){
  int k = ar[i];
  ar[i] = ar[j];
  ar[j] = k;
}

[[rc::parameters("ar : loc", "elts : {list Z}", "n : nat")]]
[[rc::args("ar @&own<array<i32, {elts `at_type` (int i32)}>>")]]
[[rc::args("n @ int<i32>")]]
[[rc::requires("{(n ≤ length elts)%nat}")]]
[[rc::returns("{n ≠ 0%nat} @ optional<\
               ∃ i : nat. i @ int<i32> & {index_of_min_list_Z (take n elts) i}, \
               {-1} @ int<i32>>")]]
[[rc::lemmas("index_of_min_list_Z_take_1")]]
[[rc::lemmas("index_of_min_list_Z_take_last")]]
[[rc::lemmas("index_of_min_list_Z_take_not_last")]]
[[rc::tactics("all: try (rewrite list_lookup_fmap H8; solve_goal).")]]
[[rc::tactics("all: try (assert (i = n) by lia; solve_goal).")]]
int min_array(int* ar, int n){
  if(n == 0) return -1;

  int res = 0;

  [[rc::exists("res : nat", "i : nat")]]
  [[rc::inv_vars("res : res @ int<i32>")]]
  [[rc::inv_vars("i : i @ int<i32>")]]
  [[rc::constraints("{(i ≤ n)%nat}")]]
  [[rc::constraints("{(res < min i n)%nat}")]]
  [[rc::constraints("{(n ≤ length elts)%nat}")]]
  [[rc::constraints("{index_of_min_list_Z (take i elts) res}")]]
  for(int i = 1; i < n; i++){
    if(ar[i] < ar[res]) res = i;
  }

  return res;
}
