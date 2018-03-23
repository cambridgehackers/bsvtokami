
KAMIDIR=../../kami

all: $(patsubst %.bsv, %.stamp, $(wildcard *.bsv))

%.stamp: %.bsv Bsvtokami.vo
	../bsvtokami $(*).bsv
	make $(*).vo
	make $(*)_proofs.vo
	touch .$(*).stamp

%.vo: %.v
	coqc -R $(KAMIDIR)/Kami Kami $< 


clean:
	rm -f .*.stamp *.vo *.glob *.pp .*.aux imports.dot
