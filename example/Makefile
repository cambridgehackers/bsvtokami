
BKDIR=?..
KAMIDIR=?../../kami/Kami

BSV_FILES = ProcMemSpec.bsv
BO_FILES = $(patsubst %.bsv,%.bo, $(BSV_FILES))

all: $(BO_FILES) out/_CoqProject out/Makefile

out:
	mkdir -p out

out/Makefile: $(BO_FILES) out
	(cd out; coq_makefile -R $KAMIDIR Kami -R $PWD BK -o Makefile *.v)

out/_CoqProject: _CoqProject out
	@cp -fv _CoqProject out

%.bo: %.bsv
	bsc $(*).bsv
