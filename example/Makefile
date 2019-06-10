
BKDIR?=..
KAMIDIR?=$(realpath ../../kami2)
BBVDIR?=$(realpath ../../bbv/theories)

BSV_FILES = ProcMemSpec.bsv PipelinedProc.bsv ProcDecExec.bsv
BO_FILES = $(patsubst %.bsv,%.bo, $(BSV_FILES))
PROOF_FILES = out/ProcDecExecOk.v
V_FILES = $(addprefix out/, $(patsubst %.bsv,%.v, $(BSV_FILES)))

all: $(BO_FILES) $(V_FILES) out/_CoqProject out/Makefile

out:
	mkdir -p out

out/Makefile: $(BO_FILES) $(PROOF_FILES) out
	echo KAMIDIR $(KAMIDIR)
	(cd out; coq_makefile -R $(KAMIDIR) Kami -R $(BBVDIR) bbv -R $(PWD)/out BK -o Makefile *.v)

out/_CoqProject: _CoqProject out
	@cp -fv _CoqProject out

%.bo: %.bsv
	@mkdir -p obj
	bsc -bdir obj -info-dir obj $(*).bsv

out/%.v: %.bo
	JAVA_OPTS=-ea $(BKDIR)/build/install/bsvtokami/bin/bsvtokami \
		-I . \
		-I $(BKDIR)/lib \
		-K out $(*).bsv
