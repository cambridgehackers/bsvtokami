
BKDIR?=..
KAMIDIR?=$(realpath ../../kami/Kami)

BSV_FILES = ProcMemSpec.bsv PipelinedProc.bsv
BO_FILES = $(patsubst %.bsv,%.bo, $(BSV_FILES))
V_FILES = $(addprefix out/, $(patsubst %.bsv,%.v, $(BSV_FILES)))

all: $(BO_FILES) $(V_FILES) out/_CoqProject out/Makefile

out:
	mkdir -p out

out/Makefile: $(BO_FILES) out
	echo KAMIDIR $(KAMIDIR)
	(cd out; coq_makefile -R $(KAMIDIR) Kami -R $(PWD)/out BK -o Makefile *.v)

out/_CoqProject: _CoqProject out
	@cp -fv _CoqProject out

%.bo: %.bsv
	bsc $(*).bsv

out/PipelinedProc.v: PipelinedProc.bo
	JAVA_OPTS=-ea $(BKDIR)/build/install/bsvtokami/bin/bsvtokami \
		-I . \
		-I $(BKDIR)/lib \
		-K out PipelinedProc.bsv
