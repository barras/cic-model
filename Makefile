
## Coq commands: override this variable
#COQBIN=$(HOME)/CONSTR/V8/bin/

COQC=$(COQBIN)coqc $(COQFLAGS)
COQ=$(COQBIN)coqtop $(COQFLAGS) -batch
COQDEP=$(COQBIN)coqdep -c
COQDOC=$(COQBIN)coqdoc

OPT=-opt
COQFLAGS=-q $(OPT) $(COQINCLUDES)
COQINCLUDES=-I .

ALLV=$(shell ls *.v)
ALLVO=$(ALLV:.v=.vo)
#COCVO = ModelHF.vo ModelZF.vo ModelECC.vo ZFindtypes.vo EnsUniv.vo ZF1.vo
ALLHTML = $(ALLV:.v=.html)

all:: coq

coq:: $(ALLVO)

html::
	mkdir -p html
	$(COQDOC) -html -d html -g $(ALLV) template/*.v
	mv html/index.html html/coqindex.html
	cp coqdoc.css html
	cp ../sets.html html/index.html

Ens0.v: Ens.v
	cp Ens.v Ens0.v


.SUFFIXES: .v .vo .ml .mli .cmo .cmi .html

.ml.cmo:
	$(CAMLC) -pp "camlp5o pa_oop.cmo" $<

.mli.cmi:
	$(CAMLC) $<

.v.vo:
	$(COQC) $<

clean::
	rm -f *~ *.vo *.glob *.cm* *.o Ens0.v coqdoc.css
	rm -fr html

depend:: Ens0.v
	rm -f .depend
	$(COQDEP) -c $(COQINCLUDES) *.v *.ml > .depend
	$(COQDEP) -suffix .html $(COQINCLUDES) *.v >> .depend

-include .depend
