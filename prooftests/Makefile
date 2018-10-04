
KAMIDIR?=$(PWD)/../../kami2

all: bsvtokami $(patsubst %.bsv, .%.stamp, $(wildcard *.bsv))

bsvtokami:
	cd ..; gradle installDist

Kami-2018-03-28a.tgz:
	curl http://buildbot.connectal.org/downloads/Kami-2018-03-28a.tgz > Kami-2018-03-28a.tgz

Kami: Kami-2018-03-28a.tgz
	tar -zxf Kami-2018-03-28a.tgz

COQARGS = -R $(KAMIDIR) Kami -R ../../bbv/theories bbv -R . BK

%.v: %.bsv
	JAVA_OPTS=-ea ../build/install/bsvtokami/bin/bsvtokami -I ../lib -I . -K $(PWD) $(*).bsv

%.vo: %.v
	#coq_makefile $(COQARGS) -o Makefile.coq *.v
	#make -f Makefile.coq $(*).vo
	echo coqc $(COQARGS) $<
	echo done

.%.stamp: %.v %.vo
	if [ -f $(*)_proofs.vo ]; then make $(*)_proofs.vo; fi
	touch .$(*).stamp

clean:
	#rm -f .*.stamp *.vo *.glob *.pp .*.aux imports.dot Makefile.coq*

vclean:
	#rm -fv `echo *.bsv | sed s/bsv/v/g`
