#!/bin/bash
S="${ARM_A_SCRATCH:?set ARM_A_SCRATCH to a scratch directory}"
cd $S/em0
for d in 140 117; do
  case $d in 140) f=drv140;; 117) f=drv117;; esac
  for O in -O0 -O2; do
    cc -std=gnu11 $O -Wall -Wextra -I$S/em0 -o $S/$f.host $S/$f.c -lpthread 2>&1 | head -5
    aarch64-linux-gnu-gcc -static -std=gnu11 $O -Wall -Wextra -I$S/em0 -o $S/$f.a64 $S/$f.c -lpthread 2>&1 | head -5
    echo "== $d $O host:  $($S/$f.host 2>&1 | tail -2 | tr '\n' ' ')"
    echo "== $d $O a64/qemu: $(qemu-aarch64 $S/$f.a64 2>&1 | tail -2 | tr '\n' ' ')"
  done
done
