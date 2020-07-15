The type system gets stuck on a sidecondition which contains an evar (i.e. protected (...)), what should I do? 
--------------------------------------------------------------------------------------------------------------

Sometimes the automation gets stuck on a goal of the form `P ∧ ...`
where `P` is some pure proposition that contains evars (marked with
`protected`). When such a goal is reached, the system automatically
applies simplification rules in the hope of reducing `P` to an
equality `x = y` which can be solved by unifying `x` and `y`. If the
type system does not know how to further simplify `P`, but it is not
yet reduced to an unifiable equality, it gets stuck. In this case
there are two options:

1. Add additional simplification rules to further simplify `P` and
   reduce it to an equality
2. Restructure the annotations such that it becomes easier for the
   type system to figure out the instantiation

Currently RefinedC does not provide a way to give a manual
instantiation of existential quantifiers, but it can be added if
necessary.

See further points in this FAQ for explanation of these options.

How do I add additional simplification rules?
---------------------------------------------

The simplification rules can be extended by the user through special
typeclasses such as `SimplBoth`, `SimplAnd` and `SimplImpl`. See the
file `theories/typing/automation.v` for the definition and many
instances. Keep in mind the simplification rules should in general be
bi-implications to avoid accidentally turning a provable goal into an
unprovable.

How should I structure my annotations such that the automatic instantiation mechanism for evars works well?
-----------------------------------------------------------------------------------------------------------

Automatic instantiation of evars is a tricky problem. Some tools like
Verifast put syntactic restrictions on where evars can be introduced
to guarantee that they can always be automatically instantiated.
RefinedC does not enforce such restrictions and allows evars to be
basically used everywhere, but in turn it cannot give guarantees that
it will always be able to automatically figure out the right way to
instantiate these evars. Thus it is important to keep this problem in
mind when writing complex RefinedC annotations which involve evars. In
particular, one should think of the following:

1. Have a sense where evars will arise during type checking. The most
   common causes for evars are the `∃ x. ty` type and `exists` clauses
   of loop invariants. Sometimes (but not so often) the implicit
   existential quantifier in a refinement type without a refinement
   can also cause problems. Note that the first occurence of an evar
   will usually instantiate it so later occurences don't have to be
   considered.
   
2. Have a strategy how these evars should be instantiated. The best
   (and most common) way to force the instantiation of an evar is to
   directly use it as a refinement (we call such evars **good**
   evars). For example, `∃ x. x @ int<size_t>` is a good evar and it
   will be very easily instantiated since `subsume (n @ int<size_t>)
   (?x @ int<size_t>)` gets reduced to `n = ?x` which instantiates
   `?x` to `n`. `∃ x. (x + 1) @ int<size_t>` is not a good evar
   because the unification problem will become the more tricky `n =
   ?x + 1` where one needs to use a simplification rule. In general,
   **you should try to ensure that all your evars are good evars**.
   This might require restructuring annotations and adding new evars or constraints.
   For example, this is not a good evar:
   ```
   ∃ l. (length l) @ int<size_t>, {something which uses l}
   ```
   and should be rewritten to
   ```
   ∃ x l. x @ int<size_t>, {something which uses l} & {length l = x}
   ```
   
   If is is not possible to restructure the annotations to turn all
   evars into good evars (this can happen e.g. arrays), it is still
   important to *avoid partial instantion of evars* as this will
   require simplification rules. For example, instead of
   ```
   ∃ l, array<size_t, l.*1 `at_type` int<size_t>>, {something which uses l}
   ```
   one should write
   ```
   ∃ l1 l2, array<size_t, l1 `at_type` int<size_t>>, {something which uses zip l1 l2**
   ```
   to avoid needing to partially instantiate `?l` to something like `zip l ?l2`.
   
The main take-away is the following: **Prefer many small evars with a
clear path to instantiation and linked with additional constraints to
few large evars which require complicated reasoning to figure out how
they should be instantiated.**

How do I debug the simplification mechanism?
--------------------------------------------
When adding such simplification rules, the system may still get stuck and it
may be useful to understand why. To this aim, you can step through the proof
manually until it gets stuck
```
repeat do_step; do_finish.
```
and then enable typeclass debugging.
```
Set Typeclasses Debug.
(*Set Typeclasses Debug Verbosity 2.*)
try do_step.
```

Another option is to apply the instances manually. To start with, use the
following tactic, and then apply the tactics mentionned in the debugging log.
```
notypeclasses refine (apply_simpl_and _ _ _ _ _)
```

Why does `ContainsProtected` contain an evar?
----------------------------------------------

Simplification rules will sometimes have an argument of the following form:
```
`{!ContainsProtected (some coq term)}
```
Do not forget the `!` here. Otherwise weird things happen.

Why don't I get as an hypothesis that an integer parameter is in range?
-----------------------------------------------------------------------

The hypotheses that the integer parameters are in range are only added to the
context on the first time the parameter is accessed. If such an hypothesis is
required prior to a first access, you can use the following macro to make it
available.
```c
rc_unfold_int(i);
```


