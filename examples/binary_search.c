#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

//@rc::import binary_search_extra from refinedc.examples.binary_search

typedef bool (*comp_fn)(void *, void *);

[[rc::parameters("R: {Z → Z → Prop}", "ls : {list Z}", "x : Z", "p : loc", "ty : {Z → type}")]]
[[rc::args("p @ &own<array<LPtr, {(fun x => &own (ty x) : type) <$> ls}>>", "{length ls} @ int<i32>",
           "&own<{ty x}>", "function_ptr<{fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ boolean bool_it; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝}>")]]
[[rc::requires("{StronglySorted R ls}", "{Transitive R}")]]
[[rc::exists("n : nat")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("{∀ i y, (i < n)%nat → ls !! i = Some y → R y x}",
              "{∀ i y, (n ≤ i)%nat → ls !! i = Some y → ¬ R y x}")]]
[[rc::ensures("p @ &own<array<LPtr, {(fun x => &own (ty x) : type) <$> ls}>>")]]
[[rc::tactics("all: try by [revert select (∀ i j, _ → _ → ¬ R _ _); apply; [| done];solve_goal].")]]
[[rc::tactics("all: try by apply: (binary_search_cond_1 y); solve_goal.")]]
[[rc::tactics("all: try by apply: (binary_search_cond_2 y); solve_goal.")]]
int binary_search(void **xs, int n, void *x, comp_fn comp) {
  int l = 0, r = n;
  [[rc::exists("vl : nat", "vr : nat")]]
  [[rc::inv_vars("l : vl @ int<i32>", "r : vr @ int<i32>")]]
  [[rc::constraints("{vl <= vr}", "{vr <= length ls}")]]
  [[rc::constraints("{∀ i y, (i < vl)%nat → ls !! i = Some y → R y x}",
                    "{∀ i y, (vr ≤ i)%nat → ls !! i = Some y → ¬ R y x}")]]
  while(l < r) {
    int k = l + (r - l) / 2;
    if (comp(xs[k], x)) {
      l = k + 1;
      } else {
      r = k;
    }
  }
  return l;
}
