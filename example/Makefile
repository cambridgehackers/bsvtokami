

all: ProcMemSpec.bo out/_CoqProject

out/_CoqProject: _CoqProject
	mkdir -p out
	cp -fv _CoqProject out

%.bo: %.bsv
	bsc $(*).bsv
