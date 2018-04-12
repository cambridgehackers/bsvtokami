
KAMIDIR?=~/kami

all: $(patsubst %.bsv, .%.stamp, $(wildcard *.bsv)) Kami

Kami-2018-03-28a.tgz:
	curl http://buildbot.connectal.org/downloads/Kami-2018-03-28a.tgz > Kami-2018-03-28a.tgz

Kami: Kami-2018-03-28a.tgz
	tar -zxf Kami-2018-03-28a.tgz

%.v: %.bsv Bsvtokami.vo Kami
	JAVA_OPTS=-ea ../build/install/bsvtokami/bin/bsvtokami -I../lib $(*).bsv

.%.stamp: %.v Bsvtokami.vo
	$(MAKE) $(*).vo
	$(MAKE) $(*)_proofs.vo
	touch .$(*).stamp

%.vo: %.v
	coqc -R $(KAMIDIR)/Kami Kami $< 


clean:
	rm -f .*.stamp *.vo *.glob *.pp .*.aux imports.dot
