
## Coq commands: override this variable
#COQBIN=$(HOME)/CONSTR/V8/bin/

COQC=$(COQBIN)coqc $(COQFLAGS)
COQ=$(COQBIN)coqtop $(COQFLAGS) -batch
COQDEP=$(COQBIN)coqdep -c
COQDOC=$(COQBIN)coqdoc
COQMK=$(COQBIN)coq_makefile

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

DOCHTML=$(shell cat libs.txt)
DOCV=$(DOCHTML:.html=.v)
#DOCV=$(shell sed -n -e "s|.*HREF=\"\([^\./\"]\+\)\.html\".*|\1.v|p" template/html/index.html)
DOCVO=$(DOCV:.v=.vo)

ALLV:=$(DOCV)

doc:: $(DOCV:.v=.vo)

.PHONY: html dist-v graph doc

dist-v::
	rm -fr cic-model
	mkdir cic-model
	cp $(DOCV) template/Make cic-model/
	mkdir cic-model/template
	cp template/Library.v cic-model/template/
	echo $(DOCV) >> cic-model/Make
	(cd cic-model && $(COQMK) -f Make > Makefile)
	tar zcvf cic-model.tgz cic-model
	(cd cic-model && $(MAKE) && $(MAKE) clean)

dist-html:: $(DOCVO)
	rm -fr html
	mkdir html
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

graph::	graph/deps.png graph/deps.imap graph/graph.html

graph/deps.g:	.depend libs.txt
	graph/graph.sh lib2graph

graph/deps.dot: graph/deps.g
	graph/graph.sh graph2dot

.dot.png:
	dot -Tpng $< > $@

.dot.imap:
	dot -Tcmapx $< > $@

graph/index.html: g.html grpah/deps.imap
	sed -e "/--IMAP--/ r deps.imap" g.html > $@

Ens0.v: Ens.v
	cp Ens.v Ens0.v
EnsEm0.v: EnsEm.v
	cp EnsEm.v EnsEm0.v


.SUFFIXES: .v .vo .ml .mli .cmo .cmi .html .dot .imap .png

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
