# Information for RefinedC developers

## Installation for development

Assumes a working install of `opam` with at least version 2.0.0 (see
https://opam.ocaml.org/doc/Install.html for installation
instructions), run the following commands in a fresh checkout of
RefinedC to get at working setup suitable for development of RefinedC
and building the examples in this repository:

```
opam switch create . ocaml-base-compiler.4.11.1
sudo apt-get install libmpfr-dev # Implicit Cerberus dependency.
opam repo add coq-released "https://coq.inria.fr/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#6ea80db048080468761499238fa0d045222ccc52"
make builddep
```

To build the files in this repository you also need to make sure that
your shell contains the correct opam environment, e.g. by running:
```
eval $(opam env)
```

## make targets

The Makefile provides the following targets:

- `make all` or `make` builds the RefinedC type system without the examples
- `make all_with_examples` builds everything including examples
- `make generate_all` uses the frontend to regenerate the Caesium code
  for all examples

## Running RefinedC on examples in this repository

The `refinedc` program form the repository can be called using `dune` with the
following command.
```bash
dune exec -- refinedc
```
Note however that you should **always** use the `--no-build` option for the
`check` command. The reason is that `refinedc check` calls `dune`, and under
the `dune` environment one should not call `dune`.
```bash
# !!!INVALID!!!
dune exec -- refinedc check examples/queue.c

# Alternative
./build.sh examples/queue.c

# Equivalent to the following valid command sequence.
dune exec -- refinedc check --no-build examples/queue.c
cd examples/proofs/queue
dune build
cd -
```

To generate the Coq code for all the examples of the repository you can run
`make generate_all`. You can also force the generation of all the generated
code using `make -B generate_all`.

## Emacs setup

The following elisp function enables direct execution of the `build.sh` script in this repo from emacs.
It searches for a `build.sh` file in parent directories of the current file and executes it with the name
of the current file. A similar functionallity should be easy to add to other editors as well.
This script binds `build` to the keys `C-c c`. Use at your own risk!

```elisp
(setq build-file-name "build.sh")
(defun build ()
  "Search in the current and parent directories for a file with the name of variable `build-file-name' and execute the first file it find."
  (interactive)
  (save-some-buffers t) ; save all buffers
  (let ((buildfile (locate-dominating-file default-directory build-file-name)))
    (unless buildfile (error "No build file found!"))
    (let ((default-directory buildfile))
      (compile (concat buildfile build-file-name " " (buffer-file-name))))
    (select-window (get-buffer-window "*compilation*"))))
(global-set-key (kbd "C-c c") 'build)
```