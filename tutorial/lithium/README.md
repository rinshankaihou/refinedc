# Lithium by Example

This folder shows how to build a Lithium-based verifier for a simple functional tutorial language.
The files in this folder are based on the explanation in Part I of Michael Sammler's thesis and are best read together with the thesis.
The main file in this folder is the following:

- [tutorial.v](tutorial.v): This is the main file of this tutorial
  that builds the Lithium-based verifier for the tutorial language.

The tutorial language is defined in the following files:

- [lang.v](lang.v): This file defines the syntax and operational
  semantics for the language used by this tutorial.

- [notation.v](notation.v): This file defines some syntactic sugar for
  constructs of the language via Coq notations.

The rest of the files ([primitive_laws.v](primitive_laws.v),
[class_instances.v](class_instances.v), [tactics.v](tactics.v))
instantiate Iris for this language. See
https://github.com/tchajed/iris-simp-lang for an explanation of the
purpose of these files.
