# RefinedC verification framework

This repository contains the source code of **RefinedC**, a foundational
verification framework targeted at idiomatic C code. Thanks to its frontend
`rcgen` (written in OCaml), RefinedC automatically translates annotated C
source code into a deep embedding of our **Caesium** C semantics in Coq,
together with corresponding function specs expressed using ownership and
refinement types. After this generation step, the RefinedC automation (built
using our **Lithium** logic programming framework) takes over to prove the
user-defined function specs (which can encode full functional correctness),
leaving possible (pure) side-conditions to the user. To resolve such
side-conditions, the user can either extend the RefinedC automation or
discharge them directly using an interactive Coq proof. The RefinedC type
system itself is also extensible to allow expert users to add support for
specific programming idioms through new typing rules. Such additions must be
proven sound against the RefinedC semantic model, which is encoded in the
[Iris](https://gitlab.mpi-sws.org/iris/iris) framework for higher-order
concurrent separation logic.

## Building RefinedC

RefinedC is known to compile with Coq 8.11.2, but the frontend currently only
builds using OCaml 4.07.1. To avoid issues with other OCaml tools we highly
recommend building RefinedC against a specific Opam switch by following the
following instructions.

**Note:** All commands should be run inside the RefinedC repository.

**Note:** This was only tested on a 64-bits Linux machine. (Although it may
possibly work on MacOS as well.)

### Setting up [opam](https://opam.ocaml.org/doc/Install.html)

First, make sure that the OCaml package manager `opam` is installed. To do
so you can run the following command.
```bash
opam --version
```
If you already have `opam` version 2.0.0 or higher then you can skip to the
next section.

Otherwise, install `opam` using your usual package manager (checking that a
recent enough version is available), or run the following command (taken from
the [official installation guide](https://opam.ocaml.org/doc/Install.html)).
```bash
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
You can use the `BINDIR` environment variable to choose where the binary is
installed. There is a reasonable default but it needs root privileges.

### Setting up an [opam](https://opam.ocaml.org) switch

After having made sure that `opam` version 2.0.0 or higher is available, you
can create a "switch" (i.e., a virtual environment for a specific version of
the OCaml compiler and a specific set of installed libraries).
```bash
opam switch create --no-install . ocaml-base-compiler.4.07.1
```

**Note:** It may be necessary to run `eval $(opam env)` inside the RefinedC
directory to setup the switch in another terminal. This is not necessary in
the terminal used for creating the switch.

**Note:** The frontend requires a C compile (accessible through `cc`).

### Installing dependencies

The first thing to do is to set up repositories:
```bash
opam pin add -n -y cerberus git+https://github.com/rlepigre/cerberus.git#da87de09974dd4063c0b50fea7f23420374dd169
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -n -y refinedc .
opam pin add -n -y refinedc-rcgen .
```

You can then install the dependencies:
```bash
opam install --deps-only refinedc refinedc-rcgen
```

**Note:** You can use `opam update && make update-deps && make clean`
to install the right version of the dependencies if the requirements
have changed. This should typically done if the version of Iris on
which RefinedC relies has been updated.

### Building

To compile the Coq source files of RefinedC run:
```bash
# Replace 8 by the number of CPUs you can spare.
make -j8 all_without_examples
```
(Using `make` will compile all the examples as well and this takes a while.)

Although this is not necessary, you can compile the frontend using:
```bash
dune build
```
(The frontend is compiled if necessary when it is called.)

### Sourcing the commands

To finish setting up RefinedC, run the following command to extend your
current shell with two new commands `rcgen` and `refinedc`:
```bash
export PATH=$(pwd)/scripts:$PATH
```
The `rcgen` command is a simple wrapper around the frontend (use the `--help` option
to see how it is used). It can be used to generate the Coq files corresponding
to an annotated C source file.

The `refinedc` command is a higher-level wrapper around the frontend. When
called on a C source file of the repository, it generates the corresponding
Coq files (that need to be updated), and also compiles them.

**NOTE:** Although these commands will be available everywhere, they only
work under the RefinedC source tree.

## Verifying Programs using RefinedC

After having installed the dependencies and compiled the Coq development a
first time (with `make -j8 all_without_examples`), the typical way to interact
with the system is to simply edit some C file and to run the `refinedc`
command on it.

A good starting point to get a hang of the system is to explore the examples
of the `examples/tutorial` directory. Feel free to edit them, break them, and
also try to extend them with new functions. After having modified, say, file
`examples/tutorial/t1_basic.c`, run `refinedc examples/tutorial/t1_basic.c`
to check the full example.

If you want to start a new example from scratch, create a new directory under
`examples`, create the C file, and just call `refinedc` on it. Note that if
you need to define things in Coq you can do so in the directory, `refinedc`
will take care of the dependencies.

The RefinedC annotation syntax is documented in file `ANNOTATIONS.md`. Note
that you will need to add the following preprocessor directive to get access
to the RefinedC macros.
```c
#include "../inc/refinedc.h"
```

## Structure of the development

The structure of the development under `theories` is as follows:

- `lang`: Caesium formalization of C and Iris instantiation
- `lithium`: Lithium definition and interpreter
- `typing`: RefinedC type system
- `examples`: examples which use RefinedC

## Common Problems

- The build fails after removing a C function: manually delete the `*_proof.*`
  files corresponding to that function in the directory where the source file
  is placed.

- `Compiled library refinedc.lang.base (in file .../theories/lang/base.vo) makes inconsistent assumptions over library stdpp.base`: This error can occur after updating the Iris dependency. Use `make clean` to resolve it.
