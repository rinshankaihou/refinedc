all:
	@dune build _build/default/refinedc.install
.PHONY: all

clean:
	@dune clean
.PHONY: clean

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

C_SRC = $(wildcard examples/*.c) $(wildcard tutorial/*.c)

%.c.gen: %.c
	@dune exec -- refinedc check --no-build $<
	@touch $@

generate_all: $(addsuffix .gen, $(C_SRC))

build-dep-opamfiles: build-dep/opam
	@true
.PHONY: build-dep-opamfiles

# Create a virtual Opam package with the same dependencies as RefinedC.
build-dep/opam: refinedc.opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@head -n -5 $< > $@
	@sed -i -E 's/^name: *"(.*)" */name: "\1-builddep"/' $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedC are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedC package itself (which takes time).
build-dep: build-dep/opam
	@echo "# Installing build-dep package."
	@opam install $(OPAMFLAGS) build-dep/

# FIXME
#%.generate: % phony
#	./scripts/rcgen $<
#	@touch $@
#
#ALL_EXAMPLES_GENERATE = $(wildcard theories/examples/*/*.generate)
#ALL_TUTORIAL_GENERATE = $(wildcard theories/examples/tutorial/*.generate)
#
#.PHONY: all_examples all_tutorial
#all_examples: $(ALL_EXAMPLES_GENERATE)
#all_tutorial: $(ALL_TUTORIAL_GENERATE)
#
#TUTORIAL_SRC = \
#	theories/examples/tutorial/t3_list.c \
#	theories/examples/tutorial/t4_alloc.c \
#	theories/examples/tutorial/t5_main.c \
#	theories/examples/spinlock/spinlock.c
#
#theories/examples/tutorial/tutorial: $(TUTORIAL_SRC)
#	clang -fdouble-square-bracket-attributes -Wno-unknown-attributes -g -O0 $^ -o $@
