# Permit local customization
-include Makefile.local

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find theories tests exercises solutions \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete || true
	rm -f Makefile.coq .lia.cache
	dune clean
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq $(EXTRA_COQFILES)

# Install build-dependencies
build-dep/opam: refinedc.opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <refinedc.opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing build-dep package."
	@opam install $(OPAMFLAGS) build-dep/

update-deps: refinedc.opam refinedc-rcgen.opam
	opam pin add -n -y refinedc .
	opam pin add -n -y refinedc-rcgen .
	opam install --working-dir --deps-only refinedc refinedc-rcgen
.PHONY: update-deps

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
%.opam: ;
Makefile.local: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
