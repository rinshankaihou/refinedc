#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include <alloc.h>

//@rc::import binary_search_extra from refinedc.examples.binary_search

typedef bool (*comp_fn)(void *, void *);

[[rc::parameters("R : {Z → Z → Prop}", "ls : {list Z}", "x : Z", "p : loc", "ty : {Z → type}", "px : loc")]]
[[rc::args("function_ptr<{fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ boolean bool_it; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝}>",
      "p @ &own<array<void*, {(fun x => &own (ty x) : type) <$> ls}>>", "{length ls} @ int<i32>", "px @ &own<{ty x}>")]]
[[rc::requires("{StronglySorted R ls}", "{Transitive R}")]]
[[rc::exists("n : nat")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("{∀ i y, (i < n)%nat → ls !! i = Some y → R y x}",
              "{∀ i y, (n ≤ i)%nat → ls !! i = Some y → ¬ R y x}")]]
[[rc::ensures("own p : array<void*, {(fun x => &own (ty x) : type) <$> ls}>")]]
[[rc::ensures("own px : ty<x>")]]
[[rc::tactics("all: try by [revert select (∀ i j, _ → _ → ¬ R _ _); apply; [| done];solve_goal].")]]
[[rc::tactics("all: try by apply: (binary_search_cond_1 y); solve_goal.")]]
[[rc::tactics("all: try by apply: (binary_search_cond_2 y); solve_goal.")]]
int binary_search(comp_fn comp, void **xs, int n, void *x) {
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

[[rc::parameters("x : Z", "y : Z", "px : loc", "py : loc")]]
[[rc::args("px @ &own<x @ int<size_t>>", "py @ &own<y @ int<size_t>>")]]
[[rc::exists("b : bool")]]
[[rc::returns("b @ boolean<bool_it>")]]
[[rc::ensures("own px : x @ int<size_t>", "own py : y @ int<size_t>", "{b ↔ Z.le x y}")]]
bool compare_int(void *x, void *y) {
  size_t *xi = x, *yi = y;
  return *xi <= *yi;
}

[[rc::requires("[alloc_initialized]")]]
[[rc::tactics("all: try by repeat constructor; lia.")]]
[[rc::tactics("all: try by apply _.")]]
[[rc::tactics("all: try by do 4 (destruct x'; [ naive_solver lia |]); exfalso; apply: (H0 3%nat) => //; lia.")]]
void test() {
  size_t *ptrs[5];
  ptrs[0] = alloc(sizeof(size_t));
  ptrs[1] = alloc(sizeof(size_t));
  ptrs[2] = alloc(sizeof(size_t));
  ptrs[3] = alloc(sizeof(size_t));
  ptrs[4] = alloc(sizeof(size_t));
  *ptrs[0] = 0;
  *ptrs[1] = 1;
  *ptrs[2] = 2;
  *ptrs[3] = 3;
  *ptrs[4] = 4;

  size_t needle = 2;
  int res = binary_search(compare_int, (void **)ptrs, 5, &needle);
  assert(res == 3);

  free(sizeof(size_t), ptrs[0]);
  free(sizeof(size_t), ptrs[1]);
  free(sizeof(size_t), ptrs[2]);
  free(sizeof(size_t), ptrs[3]);
  free(sizeof(size_t), ptrs[4]);
}
