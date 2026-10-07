#!/bin/bash
# usage: emit_all.sh BIN OUTDIR   (run from the worktree root)
BIN=$1; OUT=$2; mkdir -p $OUT
: > $OUT/emit.txt
for f in beispiele/*.gab; do
  b=$(basename $f .gab)
  if $BIN emit $f > $OUT/$b.c 2> $OUT/$b.err; then
    echo "$b ok" >> $OUT/emit.txt
  else
    echo "$b FAIL" >> $OUT/emit.txt
    rm -f $OUT/$b.c
  fi
done
