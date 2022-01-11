ISABELLE=/opt/Isabelle2021-1/bin/isabelle

document.pdf outline.pdf : $(wildcard *.thy) ROOT
	$(ISABELLE) document -P . -d . Quantum_Luby_Rackoff

isabelle :
	$(ISABELLE) jedit -d . -l Lots-Of-Stuff LR3_Compressed.thy &
