FILES = \
	Flocq_version.v \
	Core/Fcore_Raux.v \
	Core/Fcore_Zaux.v \
	Core/Fcore_defs.v \
	Core/Fcore_digits.v \
	Core/Fcore_float_prop.v \
	Core/Fcore_FIX.v \
	Core/Fcore_FLT.v \
	Core/Fcore_FLX.v \
	Core/Fcore_FTZ.v \
	Core/Fcore_generic_fmt.v \
	Core/Fcore_rnd.v \
	Core/Fcore_rnd_ne.v \
	Core/Fcore_ulp.v \
	Core/Fcore.v \
	Calc/Fcalc_bracket.v \
	Calc/Fcalc_digits.v \
	Calc/Fcalc_div.v \
	Calc/Fcalc_ops.v \
	Calc/Fcalc_round.v \
	Calc/Fcalc_sqrt.v \
	Prop/Fprop_div_sqrt_error.v \
	Prop/Fprop_mult_error.v \
	Prop/Fprop_plus_error.v \
	Prop/Fprop_relative.v \
	Prop/Fprop_Sterbenz.v \
	Appli/Fappli_IEEE.v \
	Appli/Fappli_IEEE_bits.v

EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob)

datadir = $(libdir)

all: $(FILES:=o)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I Core -I Calc -I Prop -I Appli $< > $@

SUFFIXES = .v .vo .vd

install-data-local:
	@$(NORMAL_INSTALL)
	@test -z "$(datadir)" || \
	for p in Core Calc Prop Appli; do \
	  $(MKDIR_P) "$(DESTDIR)$(datadir)/$$p"; \
	done
	@list='$(FILES:=o)'; test -n "$(datadir)" || list=; \
	for p in $$list; do \
	  if test -f "$$p"; then d=; else d="$(srcdir)/"; fi; \
	  echo "$$d$$p" "$(DESTDIR)$(datadir)/$$p"; \
	done | \
	while read src dst; do \
	  echo " $(INSTALL_DATA) $$src $$dst"; \
	  $(INSTALL_DATA) "$$src" "$$dst" || exit $$?; \
	done

uninstall-local:
	@$(NORMAL_UNINSTALL)
	test -z "$(datadir)" || rm -rf "$(DESTDIR)$(datadir)/$$p"

html: $(FILES:=o)
	@mkdir -p ../html
	$(COQDOC) -toc -g -R . Flocq -d ../html -t 'Flocq' --coqlib 'http://coq.inria.fr/library/' $(FILES)

-include $(FILES:=d)
