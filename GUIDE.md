# WIP: Guide for RefinedC developers

This guide has two parts: First, a guide for writing typing rules.
Second, a style guide for RefinedC development.

## Rule guide

1. `SimplifyHyp` and `SimplifyGoal` rules should match: The
   information learned by the `SimplifyHyp` rule should be enough to
   prove the `SimplifyGoal`. Said another way, applying the
   `SimplifyHyp` instance and then proving `SimplifyGoal` should be
   equivalent to not using any of the two (except for learning more
   information).
2. If there are multiple `SimplifyHyp` or `SimplifyGoal` rules for the
   same proposition, one must ensure that the ones with the smaller
   number also have the smaller priority on the typeclass.

## Style guide

1. Follow the std++/Iris style except when noted otherwise below. In
   particular, do the following:
  - Only use `Lemma`, not any of the other variants like `Fact` or
    similar.
  - Specify all types in Definitions, both for arguments and for the
    Definition itself.
  - Use std++'s typeclasses to overload existing notations (e.g.
    `ElemOf` for `∈`).
  - Type parameters should use captial latin letters, starting from A
    and should usually be implicit.
  - Use `done` or `by ...` to solve trivial goals. It replaces
    `reflexivity`, `trivial`, `assumption`, ...
2. Prefer the ssreflect tactics to the Coq tactics. I.e. use `move =>
   ...` instead of `intros ...`, `have ... : ...` instead of `assert`,
   `have ... := ...` instead of `pose proof`, `move Heq: (...) => ?`
   instead of `remember` and so on. See
   https://coq.inria.fr/distrib/current/refman/proof-engine/ssreflect-proof-language.html
   for documentation on ssreflect.
3. Use std++ where possible. E.g. use `f <$> l` instead of `map f l`.
4. If there is a typeclass to restrict when a typing rule applies, but
   it does not contain useful information for proving the typing rule,
   it should only be on the instance, not the lemma.
