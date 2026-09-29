#!/bin/bash
# The lock invariant in the duty channel, with its probes (GabbroV lane, 2026-09-29).
#
# `locks L { … }` on a lock with an `invariant` is an ACQUIRE (the protected carriers arrive
# with the invariant holding) and a RELEASE (a call whose precondition is the invariant).
#
#   157   a worker pool, `arbeiter` calls `setze` (requires the invariant) under the lock
#         -- OWED before, GREEN by the generator now                       GREEN  exit 0
#   124   the same with a private table: one frame chain left to a person  GREEN  exit 0
#   probe `ehrlich` closes by itself, `verlaesst_sich` promises more than the invariant
#         says and must stay OWED                                          OWED   exit 1
cd "$(dirname "$0")/.." || exit 2
G=${GABBRO:-target/release/gabbro}
[ -x "$G" ] || { echo "no $G -- cargo build --release first"; exit 2; }
free -g | sed -n 2p
rot=0
probe() { # file, expected exit, expected word
  local aus rc
  aus=$("$G" prove "$1" 2>&1); rc=$?
  if [ "$rc" = "$2" ] && echo "$aus" | grep -q "$3"; then echo "  ok   $1  ($3, exit $rc)"
  else echo "  FAIL $1  expected $3 / exit $2, got exit $rc:"; echo "$aus" | head -4; rot=$((rot+1)); fi
}
probe beispiele/157-worker-pool.gab 0 GREEN
probe beispiele/124-two-threads-private.gab 0 GREEN
probe messung/proben/probe-sperre-bricht-invariante.gab 1 'verlaesst_sich_meets_statement'
echo "lock-invariant probes failed: $rot"
[ "$rot" = 0 ]
