all:
	@dune build _build/default/refinedc.install --display short
.PHONY: all

all_with_examples: generate_all
	@dune build --display short
.PHONY: all_with_examples

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

C_SRC = $(wildcard examples/*.c) $(wildcard examples/VerifyThis2021/*.c) $(wildcard tutorial/*.c) $(wildcard tutorial/VerifyThis/*.c) $(wildcard linux/casestudies/*.c) $(wildcard linux/pkvm/*.c) $(wildcard examples/scheduler/src/fdsched.c)

%.c.gen: %.c phony
	@dune exec -- refinedc check $<
.PHONY: phony

generate_all: $(addsuffix .gen, $(C_SRC))
.PHONY: generate_all

check_generate_all: generate_all
	git diff --exit-code
.PHONY: check_generate_all

clean_generated:
	@for FILE in ${C_SRC} ; do dune exec -- refinedc clean --soft $$FILE ; done
	@rm -f $(addsuffix .gen, $(C_SRC))
.PHONY: clean_generated

clean: clean_generated
	@dune clean
.PHONY: clean

builddep-pins:
	@opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#6667765c3f1faa2d0ca3427bb4ed5fef1c63cb2b"
.PHONY: builddep-pins

builddep-opamfiles: builddep/refinedc-builddep.opam builddep-pins
	@true
.PHONY: builddep-opamfiles

# see https://stackoverflow.com/a/649462 for defining multiline strings in Makefiles
define BUILDDEP_OPAM_BODY
opam-version: "2.0"
name: "refinedc-builddep"
synopsis: "---"
description: """
---
"""
license: "BSD-3-Clause"
maintainer: ["Michael Sammler <msammler@mpi-sws.org>"
             "Rodolphe Lepigre <lepigre@mpi-sws.org>"]
authors: ["Michael Sammler" "Rodolphe Lepigre"]
homepage: "https://plv.mpi-sws.org/refinedc"
bug-reports: "https://gitlab.mpi-sws.org/iris/refinedc/issues"
dev-repo: "git+https://gitlab.mpi-sws.org/iris/refinedc.git"
depends: [
endef
export BUILDDEP_OPAM_BODY

# Create a virtual Opam package with the same deps as RefinedC, but no
# build.
builddep/refinedc-builddep.opam: refinedc.opam coq-lithium.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@echo "$$BUILDDEP_OPAM_BODY" > $@
	@opam show -f depends: ./coq-lithium.opam >> $@
	@opam show -f depends: ./refinedc.opam | sed 's/"coq-lithium".*//g' >> $@
	@echo "]" >> $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedC are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedC package itself (which takes time).
builddep: builddep/refinedc-builddep.opam builddep-pins
	@echo "# Installing package $<."
	@opam install $(OPAMFLAGS) $<
.PHONY: builddep

DUNE_FILES = $(shell find theories/ -type f -name 'dune')

# We need to remove lithium from the theories in dune files when
# installing RefinedC via opam as otherwise dune does not use the
# already installed version of Lithium, but recompiles it (if one
# instructs it with dune build -p refinedc,coq-lithium).
prepare-install-refinedc:
	@for f in $(DUNE_FILES) ; do \
		sed 's/^.*; removed by make prepare-install-refinedc.*//g' "$$f" > "$$f-tmp"; \
		mv "$$f-tmp" "$$f"; \
	done
.PHONY: prepare-install

# FIXME
#TUTORIAL_SRC = \
#	theories/examples/tutorial/t3_list.c \
#	theories/examples/tutorial/t4_alloc.c \
#	theories/examples/tutorial/t5_main.c \
#	theories/examples/spinlock/spinlock.c
#
#theories/examples/tutorial/tutorial: $(TUTORIAL_SRC)
#	clang -fdouble-square-bracket-attributes -Wno-unknown-attributes -g -O0 $^ -o $@
