#!/bin/bash

BKDIR=$PWD/..
KAMIDIR=$PWD/../../kami/Kami

(cd $BKDIR; gradle installDist) && \
    rm -f bsvtokami.log && \
    JAVA_OPTS=-ea $BKDIR/build/install/bsvtokami/bin/bsvtokami \
	     -I . \
	     -I $BKDIR/lib \
	     -K out PipelinedProc.bsv; \

mkdir -p out
cp -f $BKDIR/prooftests/Bsvtokami.v out
(cd out; coq_makefile -R $KAMIDIR Kami -R $PWD BK -o Makefile *.v)
grep Assertion bsvtokami.log
