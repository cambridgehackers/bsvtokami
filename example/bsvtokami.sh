#!/bin/bash

BKDIR=$PWD/..
KAMIDIR=$PWD/../../kami2
BBVDIR=$PWD/../../bbv

(cd $BKDIR; gradle installDist) && \
    rm -f bsvtokami.log && \
    JAVA_OPTS=-ea $BKDIR/build/install/bsvtokami/bin/bsvtokami \
	     -I . \
	     -I $BKDIR/lib \
	     -K out ProcMemSpec.bsv; \
    JAVA_OPTS=-ea $BKDIR/build/install/bsvtokami/bin/bsvtokami \
	     -I . \
	     -I $BKDIR/lib \
	     -K out ProcDecExec.bsv; \

mkdir -p out
# cp -f $BKDIR/prooftests/Bsvtokami.v out
grep Assertion bsvtokami.log
