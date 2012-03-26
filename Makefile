
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
ALLHTML = $(ALLV:%.v=html/%.html)
ALLHTMLFULL = $(ALLV:%.v=html/full/%.html)

all:: coq

coq:: $(ALLVO)

DOCV=$(shell sed -n -e "s|.*HREF=\"\([^\./\"]\+\)\.html\".*|\1.v|p" template/html/sets.html)
DOCVO=$(DOCV:.v=.vo)

.PHONY: html

src-html:: $(DOCVO)
	$(MAKE) html
html::
	mkdir -p html/full
	$(COQDOC) -utf8 -html -d html -g --coqlib http://coq.inria.fr/stdlib template/coqdoc.v $(ALLV)
	$(COQDOC) -utf8 -html -d html/full --coqlib http://coq.inria.fr/stdlib template/coqdoc.v $(ALLV)
	mv html/index.html html/coqindex.html
	/bin/cp template/html/*.* html/
	/bin/cp template/html/full/*.* html/full/
	/bin/cp html/coqdoc.css html/full/
	perl -pi -e "s/(<div id=\"header\">)/\1<script src=\"headings.js\"><\/script>/" $(ALLHTML) $(ALLHTMLFULL)

Ens0.v: Ens.v
	cp Ens.v Ens0.v
EnsEm0.v: EnsEm.v
	cp EnsEm.v EnsEm0.v


.SUFFIXES: .v .vo .ml .mli .cmo .cmi .html

.ml.cmo:
	$(CAMLC) -pp "camlp5o pa_oop.cmo" $<

.mli.cmi:
	$(CAMLC) $<

.v.vo:
	$(COQC) $<

clean::
	rm -f *~ *.vo *.glob *.cm* *.o Ens0.v
	rm -fr html

depend:: Ens0.v
	rm -f .depend
	$(COQDEP) -c $(COQINCLUDES) *.v *.ml > .depend
	$(COQDEP) -suffix .html $(COQINCLUDES) *.v >> .depend

-include .depend
