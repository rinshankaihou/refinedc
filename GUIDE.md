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

## Style guide

1. Follow the std++/Iris style.
2. If there is a typeclass to restrict when a typing rule applies, but
   it does not contain useful information for proving the typing rule,
   it should only be on the instance, not the lemma.
