#!/bin/bash
S="${ARM_A_SCRATCH:?set ARM_A_SCRATCH to a scratch directory}"
export PATH=$S/wrapbin:$PATH
export ARM_LOGDIR=$S/log-a64
cd $S
bash arm-probe.sh > a64-run.txt 2>&1
grep -c 'ARM-RESULT.*PASS' a64-run.txt
grep 'ARM-RESULT.*FAIL' a64-run.txt | cut -c1-250
tail -2 a64-run.txt
