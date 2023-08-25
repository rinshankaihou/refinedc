#include <stddef.h>
#include <stdbool.h>

//@rc::import challenge1_lemmas from refinedc.examples.VerifyThis2021.challenge1

// Verification task 1: implicitly verified
[[rc::parameters("A : {list Z}", "p : loc")]]
[[rc::args("p @ &own<array<i32, {A `at_type` int i32}>>", "{length A} @ int<i32>")]]
[[rc::requires("{0 < length A}")]]
[[rc::exists("Aret : {list Z}", "b : bool")]]
[[rc::returns("b @ builtin_boolean")]]
[[rc::ensures("own p : array<i32, {Aret `at_type` int i32}>")]]
// Verification task 4 and 5: (see Definition of next_perm in challenge1_lemmas.v)
[[rc::ensures("{next_perm A (if b then (Some Aret) else None)}")]]
// Verification task 4:
[[rc::ensures("{if b then True else A = Aret}")]]
// Verification task 3:
[[rc::ensures("{A ≡ₚ Aret}")]]

[[rc::tactics("all: try apply: next_perm_implies_perm.")]]
[[rc::tactics("all: try by apply: next_perm_end; destruct i.")]]
[[rc::tactics("all: try by apply: next_perm_next; solve_goal.")]]
[[rc::tactics("all: try by apply: Sorted_small; solve_goal.")]]
[[rc::tactics("all: try (apply: NPSStep; try (apply: next_partial_swap_mono;[done|..]); try lia; try done; rewrite Z2Nat.inj_add ?Nat.sub_1_r -?Nat.add_pred_r/= ?Nat.add_0_r ?Nat.succ_pred;[|lia..]).")]]
[[rc::tactics("all: try (apply: NPSBase => //; try lia; have <-: Z.to_nat j = e; [ by have := next_end_gt (Z.to_nat j) _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done); lia|]).")]]
[[rc::tactics("all: try by apply: swap_intro.")]]
[[rc::tactics("all: try by eexists _, _.")]]
[[rc::tactics("all: try by destruct (decide (i = j)); [ | lia]; subst; have := (next_start_lt _ _ _ _ ltac:(done) ltac:(done) ltac:(done)); lia.")]]
[[rc::tactics("all: try by eexists _; split; [done|]; destruct (decide (e = Z.to_nat j)); [subst |lia]; change (Z.to_nat 1) with 1%nat in *; revert select (next_end _ _ _) => -[?]; naive_solver lia.")]]
[[rc::tactics("all: try by erewrite drop_S => //; rewrite Nat.sub_1_r Nat.succ_pred; [|lia]; apply: Sorted_cons => //; erewrite drop_S => //; by constructor.")]]
[[rc::tactics("all: try by have [//|e ?] := next_end_exists (Z.to_nat i) A _ _ ltac:(done) ltac:(done); eexists _; split; [done| by apply: next_end_upper].")]]
bool next(int A[], int size) {
  int i = size - 1;

#define LOOP_INV \
  [[rc::exists("Acur : {list Z}", "i : Z")]] \
  [[rc::inv_vars("A : p @ &own<array<i32, {Acur `at_type` int i32}>>")]] \
  [[rc::inv_vars("i : i @ int<i32>")]] \
  [[rc::constraints("{length Acur = length A}", "{length A <= max_int i32}")]]

  LOOP_INV
  [[rc::constraints("{0 <= i < length A}")]]
  [[rc::constraints("{Sorted Z.ge (drop (Z.to_nat i) A)}")]]
  [[rc::constraints("{Acur = A}")]]
  while(i > 0 && A[i - 1] >= A[i]) {
    i = i - 1;
  }

  if (i <= 0) {
    return false;
  }

  int j = size - 1;
  LOOP_INV
  [[rc::exists("j : Z")]]
  [[rc::inv_vars("j : j @ int<i32>")]]
  [[rc::constraints("{0 < i < length A}")]]
  [[rc::constraints("{i <= j < length A}")]]
  [[rc::constraints("{∃ e, next_end (Z.to_nat i) e A ∧ e <= j}")]]
  [[rc::constraints("{next_start (Z.to_nat i) A}")]]
  [[rc::constraints("{Acur = A}")]]
  while(A[j] <= A[i-1]) {
    j = j - 1;
  }

  int temp = A[i - 1];
  A[i - 1] = A[j];
  A[j] = temp;


  j = size - 1;
  LOOP_INV
  [[rc::exists("j : Z", "s : nat")]]
  [[rc::inv_vars("j : j @ int<i32>")]]
  [[rc::constraints("{next_start s A}")]]
  [[rc::constraints("{0 < i <= j + 1}")]]
  [[rc::constraints("{s <= i}")]]
  [[rc::constraints("{j < length A}")]]
  [[rc::constraints("{next_partial_swap s (Z.to_nat i) (Z.to_nat j) Acur A}")]]
  while(i < j) {
    temp = A[i];
    A[i] = A[j];
    A[j] = temp;
    i = i + 1;
    j = j - 1;
  }

  return true;
}


typedef struct [[rc::refined_by("l: {list type}")]]
               [[rc::typedef("list_t : {maybe2 cons l} @ optionalO<λ (ty, l). &own<...>>")]]
list {
    [[rc::field("&own<ty>")]]
    void *head;

    [[rc::field("l @ list_t")]]
    struct list *tail;
} *list_t;

[[rc::returns("{[]} @ list_t")]]
list_t list_new();

[[rc::parameters("p : loc", "l : {list type}", "ty : type")]]
[[rc::args("p @ &own<l @ list_t>", "&own<ty>")]]
[[rc::ensures("own p : {l ++ [ty]} @ list_t")]]
void list_snoc(list_t *l, void *x);

[[rc::parameters("p : loc", "A : {list Z}")]]
[[rc::args("p @ &own<array<i32, {A `at_type` int i32}>>", "{length A} @ int<i32>")]]
[[rc::exists("Asorted : {list Z}")]]
[[rc::ensures("own p: array<i32, {Asorted `at_type` int i32}>")]]
[[rc::ensures("{Asorted ≡ₚ A}", "{Sorted Z.le Asorted}")]]
void sort(int A[], int size);

[[rc::parameters("p : loc", "A : {list Z}")]]
[[rc::args("p @ &own<array<i32, {A `at_type` int i32}>>", "{length A} @ int<i32>")]]
[[rc::returns("&own<array<i32, {A `at_type` int i32}>>")]]
[[rc::ensures("own p: array<i32, {A `at_type` int i32}>")]]
int *copy_array(int A[], int size);

// Verification task 6: implicitly verified
[[rc::parameters("p : loc", "A : {list Z}")]]
[[rc::args("p @ &own<array<i32, {A `at_type` int i32}>>", "{length A} @ int<i32>")]]
[[rc::exists("ps : {list (list Z)}")]]
[[rc::returns("{(λ p, (array i32 (p `at_type` int i32))) <$> ps} @ list_t")]]
[[rc::ensures("{∀ i p1 p2, ps !! i = Some p1 → ps !! (S i) = Some p2 → next_perm p1 (Some p2)}")]]
[[rc::ensures("{∀ p, last ps = Some p → next_perm p None}")]]
[[rc::ensures("{∀ A', 0 < length A → A ≡ₚ A' → A' ∈ ps}")]]
[[rc::ensures("{NoDup ps}")]]

[[rc::tactics("all: try by apply: Permutation_length.")]]
[[rc::tactics("all: try by destruct ps => //; simplify_eq/=; naive_solver.")]]
[[rc::tactics("all: try by apply: all_perms.")]]
[[rc::tactics("all: try by apply: perms_no_dup.")]]
[[rc::tactics("all: try by apply: last_snoc.")]]
[[rc::tactics("all: try by revert select (next_perm _ (Some _)) => /next_perm_implies_perm/Permutation_length; lia.")]]
[[rc::tactics("all: case_bool_decide; [case_bool_decide; [naive_solver |lia] | ].")]]
[[rc::tactics("all: revert select ([_] !! _ = _) => /list_lookup_singleton_Some[??]; subst.")]]
[[rc::tactics("all: case_bool_decide; [| lia]; simplify_eq.")]]
[[rc::tactics("all: have Heq : ps !! i = last ps by rewrite last_lookup; f_equal; lia.")]]
[[rc::tactics("all: rewrite ->Heq in *; by simplify_eq.")]]
list_t permut(int A[], int size) {
  list_t l = list_new();
  int *copy;


  if (size == 0) {
    return l;
  }

  sort(A, size);
  copy = copy_array(A, size);
  list_snoc(&l, copy);

  [[rc::exists("ps : {list (list Z)}", "Acur : {list Z}")]]
  [[rc::inv_vars("l : {(λ p, (array i32 (p `at_type` int i32))) <$> ps} @ list_t")]]
  [[rc::inv_vars("A : p @ &own<array<i32, {Acur `at_type` int i32}>>")]]
  [[rc::constraints("{∀ i p1 p2, ps !! i = Some p1 → ps !! (S i) = Some p2 → next_perm p1 (Some p2)}")]]
  [[rc::constraints("{last ps = Some Acur}", "{length Acur = length A}", "{0 < length A}")]]
  [[rc::constraints("{∃ Ahead, head ps = Some Ahead ∧ Ahead ≡ₚ A ∧ Sorted Z.le Ahead}", "{length Acur = length A}", "{0 < length A}")]]
  while(next(A, size)) {
    copy = copy_array(A, size);
    list_snoc(&l, copy);
  }


  return l;
}
