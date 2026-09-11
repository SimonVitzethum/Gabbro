#!/usr/bin/env bash
# frist-28 runner -- builds and runs the staged date probes of this directory.
#
#     messung/proben/frist-28/run.sh [--iterations N] [--calibrate]
#
# WHAT IT RUNS
# ------------
# The 14 staged probes `frist28_*.c`: 10 timed probes (default run must exit
# 0, `--max-cycles 1` must exit 1, UBSan clean) and 4 privilege-guarded probes
# (must exit 77 on a ring-three bench: the timed instruction faults).
# Exit 0 iff every probe behaves as booked; exit 1 otherwise.
# `--calibrate` runs each timed probe five times and prints the
# min/p50/p99/max lines for booking the tripwire -- it does not judge.
set -u
export LC_ALL=C

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ITERS=20000
CALIBRATE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --iterations) ITERS="$2"; shift 2 ;;
    --calibrate) CALIBRATE=1; shift ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

TIMED="scharfschalten warteschlange_scharf used_lesen bereit leitungsstand maske_setzen empfang_freigeben sende alle_anhalten halt_verteiler"
PRIV="seite_vergessen ferne_kern_wecken ausgeben melden"
CFLAGS=(-std=c11 -Wall -Wextra -Werror -O2)
UCFLAGS=(-std=c11 -Wall -Wextra -Werror -O2 -fsanitize=undefined)
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fail=0
if [ "$CALIBRATE" -eq 1 ]; then
  for p in $TIMED; do
    cc "${CFLAGS[@]}" -o "$TMP/frist28_$p" "$DIR/frist28_$p.c" || { echo "BUILD-FAIL frist28_$p"; fail=1; continue; }
    for r in 1 2 3 4 5; do
      "$TMP/frist28_$p" --iterations "$ITERS" 2>&1 | grep -E "^(probe|      cycles|      grid S)" || true
    done
  done
  exit "$fail"
fi

for p in $TIMED; do
  cc "${CFLAGS[@]}" -o "$TMP/frist28_$p" "$DIR/frist28_$p.c" 2>"$TMP/$p.build" || { echo "BUILD-FAIL frist28_$p"; sed 's/^/  /' "$TMP/$p.build"; fail=1; continue; }
  "$TMP/frist28_$p" --iterations "$ITERS" >"$TMP/$p.out" 2>&1
  rc=$?
  "$TMP/frist28_$p" --iterations "$ITERS" --max-cycles 1 >"$TMP/$p.ctl" 2>&1
  ctl=$?
  cc "${UCFLAGS[@]}" -o "$TMP/frist28_${p}_u" "$DIR/frist28_$p.c" 2>"$TMP/$p.ubuild" || { echo "UBSAN-BUILD-FAIL frist28_$p"; fail=1; continue; }
  "$TMP/frist28_${p}_u" --iterations "$ITERS" >"$TMP/$p.uout" 2>&1
  urc=$?
  line="$(grep -E '^      cycles' "$TMP/$p.out" || echo MISSING)"
  grid="$(grep -E '^      grid S' "$TMP/$p.out" || echo MISSING)"
  if [ "$rc" = "0" ] && [ "$ctl" = "1" ] && [ "$urc" = "0" ]; then
    echo "PASS frist28_$p  (run 0, control 1, ubsan 0)  $line  $grid"
  else
    echo "FAIL frist28_$p  (run $rc want 0, control $ctl want 1, ubsan $urc want 0)"
    fail=1
  fi
done

for p in $PRIV; do
  cc "${CFLAGS[@]}" -o "$TMP/frist28_$p" "$DIR/frist28_$p.c" 2>"$TMP/$p.build" || { echo "BUILD-FAIL frist28_$p"; sed 's/^/  /' "$TMP/$p.build"; fail=1; continue; }
  "$TMP/frist28_$p" --iterations "$ITERS" >"$TMP/$p.out" 2>&1
  rc=$?
  cc "${UCFLAGS[@]}" -o "$TMP/frist28_${p}_u" "$DIR/frist28_$p.c" 2>"$TMP/$p.ubuild" || { echo "UBSAN-BUILD-FAIL frist28_$p"; fail=1; continue; }
  "$TMP/frist28_${p}_u" --iterations "$ITERS" >"$TMP/$p.uout" 2>&1
  urc=$?
  line="$(grep -E 'NOT RUNNABLE HERE|REFUTED|not refuted' "$TMP/$p.out" | head -1 || echo MISSING)"
  if [ "$rc" = "77" ] && [ "$urc" = "77" ]; then
    echo "PASS frist28_$p  (77 here as booked)  $line"
  else
    echo "FAIL frist28_$p  (run $rc want 77, ubsan $urc want 77)"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "FRIST-28: ALL PASS"
else
  echo "FRIST-28: FINDING"
fi
exit "$fail"
