.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Lab1
	$(COQC) Lab2

clean:
	rm *.vo
