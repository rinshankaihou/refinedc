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

1. Follow the [std++/Iris style](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/style_guide.md) except when noted otherwise below. In
   particular, do the following:
  - Only use `Lemma`, not any of the other variants like `Fact` or
    similar.
  - Specify all types in `Definition`, both for arguments and for the
    Definition itself.
  - Use std++'s typeclasses to overload existing notations (e.g.
    `ElemOf` for `∈`).
  - Type parameters should use captial latin letters, starting from A
    and should usually be implicit.
  - Use `done` or `by ...` to solve trivial goals. It replaces
    `reflexivity`, `trivial`, `assumption`, ...
  - Don't use generated names of hypothesis.
  - Make sure that the spacing is consistent (e.g. no space before and
    one space after ",", see also Iris styleguide)
  - Use snake_case for definitions and PascalCase for typeclasses
  - Avoid overly broad names (e.g. `list_bool_to_list_int` should be
    used for a canonical function of converting `list bool` to `list
    int`, but not for a more specific function that it tailored to a
    specific use case)
  - Avoid the boolean comparison functions on integers like `<?`.
    Instead use `bool_decide (a < b)`.
  - Don't use `forall x, ...` at the beginning of `Lemma` statements. Instead
    put `x` before the `:`
  - Always use the unicode variants of forall, exists, ->, <=, >=, <> (see
    Iris styleguide).
  - Put the rewrite modifiers next to the lemma without a space, i.e. Bad: `rewrite! andb_true_l.`
    Good: `rewrite !andb_true_l.`
2. Prefer the ssreflect tactics to the Coq tactics. I.e. use `move =>
   ...` instead of `intros ...`, `have ... : ...` instead of `assert`,
   `have ... := ...` instead of `pose proof`, `move Heq: (...) => ?`
   instead of `remember` and so on. See
   https://coq.inria.fr/distrib/current/refman/proof-engine/ssreflect-proof-language.html
   for documentation on ssreflect.
3. Use std++ where possible. E.g. use `f <$> l` instead of `map f l`.
   Also use `naive_solver` instead of `intuition` or `tauto`.
4. If there is a typeclass to restrict when a typing rule applies, but
   it does not contain useful information for proving the typing rule,
   it should only be on the instance, not the lemma.
5. Use `if bool_decide P then ...` instead of `if decide P then ...`.
   This works better for automation since one can rewrite with
   `bool_decide P = true` in the first version, but not in the second
   version.
