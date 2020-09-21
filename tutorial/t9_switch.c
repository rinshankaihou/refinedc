#include "../inc/refinedc.h"

[[rc::parameters("i : nat")]]
[[rc::args("i @ int<i32>")]]
[[rc::returns("{if bool_decide (i ≤ 4)%nat then 4%nat else i} @ int<i32>")]]
int test_switch(int i){
  int o = i;

  switch (i) {
  case 0: o++;
  case 1: o++;
  case 2: o++;
  case 3: o++;
  }

  return o;
}

[[rc::parameters("i : nat")]]
[[rc::args("i @ int<i32>")]]
[[rc::requires("{i + 1 < it_max i32}")]]
[[rc::returns("{(if bool_decide (i ≤ 4) then 5 else i + 1)%nat} @ int<i32>")]]
int test_switch_default(int i){
  int o = i;

  switch (i) {
  case 0:  o++;
  case 1:  o++;
  case 2:  o++;
  case 3:  o++;
  default: o++;
  }

  return o;
}

[[rc::parameters("i : nat")]]
[[rc::args("i @ int<i32>")]]
[[rc::returns("{(if bool_decide (i ≤ 4) then i + 1 else i)%nat} @ int<i32>")]]
int incr_less_than_5(int i){
  int o = i;

  switch (i) {
  case 0:  o++; break;
  case 1:  o++; break;
  case 2:  o++; break;
  case 3:  o++; break;
  case 4:  o++; break;
  }

  return o;
}

[[rc::parameters("i : Z")]]
[[rc::args("i @ int<i32>")]]
[[rc::requires("{0 < i}", "{i + 3 < it_max i32}")]]
[[rc::returns("i @ int<i32>")]]
int duffs_identity(int i){
  int o = 0;

  int n = (i + 3) / 4;
  switch (i % 4) {
  case 0: [[rc::exists("n : Z")]]
          [[rc::inv_vars("n : n @ int<i32>")]]
          [[rc::inv_vars("o : {i - 4 * n} @ int<i32>")]]
          [[rc::constraints("{0 ≤ n}")]]
          do { o++;
  case 3:      o++;
  case 2:      o++;
  case 1:      o++;
            --n;
          } while (n > 0);
  }

  return o;
}
