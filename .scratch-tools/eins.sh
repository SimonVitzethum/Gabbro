#!/bin/bash
# usage: eins.sh Module  (inside grammatik/)
flock /home/simon/.cache/gabbro-stage0-build.slot-1.lock systemd-run --user --scope -q -p AllowedCPUs=0-11 -p CPUQuota=400% -p MemoryMax=5G -p MemoryHigh=4G -p MemorySwapMax=0 env LEAN_NUM_THREADS=4 lake build "$1" 2>&1 | grep -E -A${2:-12} '^error' | head -${3:-60}
