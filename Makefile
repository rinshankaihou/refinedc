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

C_SRC = $(wildcard examples/*.c) $(wildcard examples/VerifyThis2021/*.c) $(wildcard tutorial/*.c) $(wildcard linux/casestudies/*.c) $(wildcard linux/pkvm/*.c)

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

builddep-opamfiles: builddep/refinedc-builddep.opam
	@true
.PHONY: builddep-opamfiles

# Create a virtual Opam package with the same deps as RefinedC, but no
# build. Uses a very ugly hack to use sed for removing the last 4
# lines since head -n -4 does not work on MacOS
# (https://stackoverflow.com/a/24298204)
builddep/refinedc-builddep.opam: refinedc.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@sed '$$d' $< | sed '$$d' | sed '$$d' | sed '$$d' | sed -E 's/^name: *"(.*)" */name: "\1-builddep"/' > $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedC are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedC package itself (which takes time).
builddep: builddep/refinedc-builddep.opam
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
.PHONY: builddep

# FIXME
#TUTORIAL_SRC = \
#	theories/examples/tutorial/t3_list.c \
#	theories/examples/tutorial/t4_alloc.c \
#	theories/examples/tutorial/t5_main.c \
#	theories/examples/spinlock/spinlock.c
#
#theories/examples/tutorial/tutorial: $(TUTORIAL_SRC)
#	clang -fdouble-square-bracket-attributes -Wno-unknown-attributes -g -O0 $^ -o $@
