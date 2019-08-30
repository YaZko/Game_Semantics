COQINCLUDES= -R . Games

COQC="$(COQBIN)coqc" -q $(COQINCLUDES)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)

COQFILES := Utils Games ITrees_as_games ITrees_as_games_informative examples
VFILES := $(COQFILES:%=%.v)
VOFILES := $(COQFILES:%=%.vo)
GLOBFILES := $(COQFILES:%=%.glob)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq

coq: $(VOFILES)

depend: $(VFILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

%.vo: %.v
	@echo "COQC $*.v"
	@$(COQC) $*.v

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -f $(GLOBFILES)

