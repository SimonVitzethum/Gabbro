#!/bin/bash
# usage: cc_all.sh DIR   (run from worktree root). Compiles DIR/*.c with host cc, aarch64 gcc, clang aarch64
D=$1
: > $D/cc.txt
for c in $D/*.c; do
  b=$(basename $c .c)
  case $b in *.*) continue;; esac
  h=ok; a=ok; k=ok
  cc -std=c11 -Wall -Wextra -Werror -Ilaufzeit -c -o /dev/null $c 2> $D/$b.cc.host || h=FAIL
  aarch64-linux-gnu-gcc -std=c11 -Wall -Wextra -Werror -Ilaufzeit -c -o /dev/null $c 2> $D/$b.cc.a64 || a=FAIL
  clang --target=aarch64-linux-gnu -std=c11 -Wall -Wextra -Werror -Ilaufzeit -c -o /dev/null $c 2> $D/$b.cc.clang || k=FAIL
  echo "$b host=$h a64gcc=$a a64clang=$k" >> $D/cc.txt
done
