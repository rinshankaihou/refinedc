#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

/**
  This file discusses a kind of error that we have not seen so far: Failure
  to automatically instantiate existential quantifiers / evars.
  (See also Section 5, Handling of evars of the RefinedC PLDI'21 paper)

  The RefinedC typechecking often generate evars (e.g. for the parameters of
  a function or for existential quantifiers in loop invariants, structures or post-conditions).
  However, RefinedC must be careful when instantiating evars because a bad instantiation
  could easily make the goal unprovable. To prevent this, RefinedC seals all the evars
  it creates so that they cannot be prematurely instantiated by Coq's unification and
  then uses a set of heuristics to determine the right instantiation.

  Let's see this in action: Comment out the rc::trust_me on the function below and
  look at the resulting error.
 */

[[rc::exists("n : Z")]]
[[rc::ensures("{n > 0}")]]
[[rc::trust_me]] // comment out this line
void evar_create() {
  return;
}

/**
  You should see an error that looks like the following:

    Cannot instantiate evar in "evar_create" in block "#0" !
    Location: "tutorial/t02_evars.c" [ 25 : 2 - 25 : 9 ]
    up to date: true
    Goal:
    Q : (gmap label stmt)
    Hevar : Z
    ---------------------------------------
    (protected Hevar > 0)

  This is a new kind of error: RefinedC says that it cannot figure out the
  right instantiation for the evar [protected Hevar]. These evars are easy to
  recognize since they are marked by [protected].

  In this example, RefinedC cannot instantiate [protected Hevar] since there
  are many possible instatiations, i.e. numbers that a greater than 0.
  Let's see how we can solve this error. There are many different strategies for
  solving such an error:

  Strategy 1: Move quantifiers into sideconditions

  The evar from the example above comes from the rc::exists clause, but is only used
  in one sidecondition. So one solution to the problem above is to move the existential
  quantifier into the sidecondition. Then it is no longer managed by RefinedC, but
  instead can be instantiated by custom tactics. This can be done via the rc::tactics
  annotation as the following example shows:
 */

[[rc::ensures("{∃ n, n > 0}")]]
[[rc::tactics("all: try by exists 5; lia.")]] // comment out this line to see the sidecondition
void evar_create_sidecond() {
  return;
}

/**
  Strategy 2: Use the evar as a refinement

   The specification of the function evar_create above is a bit weird since [n]
   is only used in a sidecondition, but not tied to the return value of the
   function. So let's look at a function that ensures that it returns a value
   greater than 0.
 */

[[rc::exists("n : Z")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("{n > 0}")]]
int evar_create_return_int() {
  return 5; // try replacing the 5 with 0
}

/**
  Here RefinedC can automatically instantiate [n] and verify this function automatically.
  This is because the rc::returns clause enforces that [n] must be the value that is returned
  by the function and this fully determines the instantiation. Concretely, the following steps
  happen:

  1. Typechecking [evar_create_return_int] infers that the return value has type [5 @ int<i32>].
  2. RefinedC has to prove that the return value has type [(protected Hevar) @ int<i32>].
  3. This means that RefinedC has to prove that [5 @ int<i32>] is a subtype of
     [(protected Hevar) @ int<i32>].
  4. Proving a subtype relationship between the same type with different refinements is reduced
     to proving an equality between the refinement, i.e. [5 = protected Hevar].
       Note: This heuristic is used for all refinement types, not just int.
  5. The proof obligation [5 = protected Hevar] tells RefinedC that it should instantiate
     [protected Hevar] to 5.

  Let's have a closer look at 5. and in particular at the heuristics that RefinedC uses the instatiate
  evars. First, RefinedC only instantiates evars when it encounters equalities (i.e. for the obligation
  [protected Hevar > 0] from before, RefinedC immediately gives up since it is not an equality).
  When RefinedC encounters an equality with an evar, it first removes the [protected] and then
  tries to unify both sides of the equality (potentially instantiating evars). Though this heuristic
  is often effective, it may also turn a provable goal into an unprovable goal if it unifies an evar
  appearing as the argument of a non-injective symbol as the following example shows:
 */

[[rc::parameters("l : {list Z}")]]
[[rc::exists("lret : {list Z}")]]
[[rc::ensures("{lret = replicate (length l) 0}", "{length l = length lret}")]]
// see what happens when one uses the rc::ensures below instead of the rc::ensures above
/* [[rc::ensures("{length l = length lret}", "{lret = replicate (length l) 0}")]] */
void evar_instantiate_wrong() {
  return;
}

/**
  With the first rc::ensures clause, RefinedC first encounters the sidecondition
  [protected Hevar = replicate (length l) 0] and thus instantiates [protected Hevar] with
  [replicate (length l) 0] via unification. This instantiation allows RefinedC to prove the
  second sidecondition.

  However, with the second rc::ensures clause, RefinedC first encounters the sidecondition
  [length l = length (protected Hevar)] which can also be solved via unification, but instantiates
  [protected Hevar] to [l]. However, with this instantation the second sidecondition is no longer
  provable!

  This observation leads to another strategy:

  Strategy 3: Order sideconditions such that the condition which fully determines the instantation
    comes first.

  In particular, a side-condition like [lret = replicate (length l) 0] should come first.
  RefinedC guarantees that rc::ensures clauses and other clauses are handled from left to right.

 */

/**
  Another consequence of the heuristics above is that one has to ensure that the equalities
  involving evars can be solved by unification. This leads to another strategy:

  Strategy 5: Formulate sideconditions such that they can be solved by unification

  We will explain this strategy based on the example of a function [return_multiple_of_8] that
  returns a multiple of 8:
 */

[[rc::exists("n : Z")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("{(8 | n)}")]]
// try the following rc::returns instead of the previous rc::returns and rc::ensures
/* [[rc::returns("{n * 8} @ int<i32>")]] */
int return_multiple_of_8() {
  return 32;
}

/**
  There are two different ways to formulate the specification of [return_multiple_of_8]. The first
  option is to say that it returns an integer [n] that is divisible by 8. This gives a clear path
  to the instantiation of [n] as the rc::returns results in a sidecondition [protected Hevar = 32],
  which is easy to solve via unification.

  One can also formulate this specification such that the function returns an integer
  [n * 8]. However, as one can try above, this leads to the sidecondition [32 = protected Hevar * 8]
  which the unification algorithm is not able to solve.

  Thus, the first option is preferable to the second option, eventhough they are logically identical.
 */

/**
  However, there might be cases where it is not obvious how to formulate the sideconditions in a way
  that they can be directly solved via unification. This is why RefinedC provides a way to reduce
  complex sideconditions to simpler sideconditions that can then be solved by unification. In particular,
  when RefinedC encounters a sidecondition with evars that it cannot solve via unification, it uses a set
  of user-defined simplification rules to simplify the sidecondition. This leads to another strategy:

  Strategy 6: Add simplification rules such that the simplified sidecondition can be solved by unification

  The following example explains this strategy. Here we have a function [return_multiple_of_5] that is similar
  to the example above. However, the specification is formulated the same way as the second problematic option
  from above (by saying that it returns [n * 5]). By default, this would lead to a sidecondition
  [20 = protected Hevar * 5] which --- as we have seen -- cannot be solved via unification. However, one can
  add a simplification rule [SimplBoth (20 = n * 5) (n = 4)] which tells RefinedC to simplify equalities of the
  form [20 = n * 5] to [n = 4]. Applying this simplification results in [protected Hevar = 4], which can then
  be solved via unification.

 */

//@rc::inlined
//@Global Instance simpl_both_20_mult_5 n: SimplBoth (20 = n * 5) (n = 4).
//@Proof. split; lia. Qed.
//@rc::end

[[rc::exists("n : Z")]]
[[rc::returns("{n * 5} @ int<i32>")]]
int return_multiple_of_5() {
  return 20;
}

/**
  For some examples of simplification rules see [theories/lithium/simpl_instances.v].
 */
