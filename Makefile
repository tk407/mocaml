#!/bin/bash
# MC OCaml 

FIGS=implOut gramDep
DISSFOLDER=./Dissertation

dissertation: figures fullSemantics

figures: $(FIGS)

implOut:
	dot -Tps2 implOut.dot -o implOut.ps
	epstopdf implOut.ps
	rm -f $(DISSFOLDER)/implOut.pdf
	cp implOut.pdf $(DISSFOLDER)
gramDep:
	rm -f mconbaseDep.dot
	rm -f mconbaseDep.ps
	rm -f $(DISSFOLDER)/mconbaseDep.pdf
	ott -i mconbase.ott -dot mconbaseDep.dot
	dot -Tps2 mconbaseDep.dot -o mconbaseDep.ps
	epstopdf mconbaseDep.ps
	cp mconbaseDep.pdf $(DISSFOLDER)

fullSemantics:
	rm -f mconbase.tex
	rm -f mconbase_h.tex
	rm -f mconbase.pdf
	ott -i mconbase.ott -o mconbase_h.tex
	sed -n -e :a -e '1,9!{P;N;D;};N;ba' mconbase_h.tex | sed '1,9d' > mconbase.tex

