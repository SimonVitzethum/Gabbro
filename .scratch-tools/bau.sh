#!/bin/bash
# Phased grammar build: everything that does not reach a probe, then each probe module alone, then the rest.
cd "$(dirname "$0")/../grammatik"
L=/home/simon/.cache/gabbro-stage0-build.slot
run() { flock $L-1.lock flock $L-2.lock env -u ELAN_TOOLCHAIN systemd-run --user --scope -q -p AllowedCPUs=0-11 -p CPUQuota=1200% -p MemoryMax=14G -p MemoryHigh=12G -p MemorySwapMax=0 lake build "$@"; }
probes=$(find Grammatik -name "*Proben*.lean" | sed 's|\.lean$||; s|/|.|g' | sort)
for p in $probes; do
  echo "== $p"
  run $p > ../.scratch-bau-probe.log 2>&1 || { echo "FAIL $p"; grep -E "^error" ../.scratch-bau-probe.log | head -5; }
done
echo "== all"
run Grammatik > ../.scratch-bau-all.log 2>&1; echo "rc=$?"
grep -E "^error" ../.scratch-bau-all.log | cut -c1-200 | sort -u | head -40
