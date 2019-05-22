#!/bin/bash

BKDIR=$PWD/..

(cd $BKDIR; gradle installDist) && \
    rm -f bsvtokami.log && \
    JAVA_OPTS=-ea $BKDIR/build/install/bsvtokami/bin/bsvtokami \
	     -I . \
	     -I $BKDIR/lib \
	     -K out gcd.bsv;

mkdir -p out
# cp -f $BKDIR/prooftests/Bsvtokami.v out
grep Assertion bsvtokami.log
