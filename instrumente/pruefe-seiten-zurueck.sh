#!/usr/bin/env bash
# instrumente/pruefe-seiten-zurueck.sh -- `reset X at i count n;` GIVES PAGES BACK
# (server lane, M-ALLTAG C, 2026-09-30).
#
# THE CLAIM. A fixed buffer that was busy and is idle stops being resident: the
# range reads as zero AND the resident set (`/proc/self/statm`) falls by the
# pages of the range. Both halves are measured, on the emitted C, with the
# program's own binding (`bibliothek/linux/linux.gab`, `gabbro_os_seiten_zurueck` in Gabbro
# since 2026-09-30, C-free lane; the helper hands it the whole pages, template `region.leeren`).
#
#   1. bound  : after the give-back the buffer is all zero and RSS fell by at
#               least 3/4 of the mebibyte (the ragged ends and the rest of the
#               process stay).
#   2. unbound: WITHOUT the binding the range is still all zero (the emitted
#               loop), and RSS did NOT fall -- the page return is the binding's,
#               nothing in the emitted C or the runtime makes an OS call.
#   3. poison : a build whose `reset` statement is removed leaves the buffer
#               full and RSS up: the test of (1) turns RED. A give-back nobody
#               makes must not pass.
#
# Usage: instrumente/pruefe-seiten-zurueck.sh [--gabbro <binary>]
set -u
cd "$(dirname "$0")/.."
W=$PWD
G="${GABBRO:-$W/target/debug/gabbro}"
[ "${1:-}" = "--gabbro" ] && G="$2"
T=$(mktemp -d /tmp/seiten-zurueck.XXXXXX)
trap 'rm -rf "$T"' EXIT
fail=0
"$G" emit "$W/messung/proben/seiten-zurueck/ring.gab" > "$T/ring.c" 2> "$T/emit.err" || {
    echo "RED: emit failed"; cat "$T/emit.err"; exit 1; }
"$G" emit "$W/bibliothek/linux/linux.gab" > "$T/linux_bind.c" 2> "$T/emit2.err" || {
    echo "RED: the binding did not emit"; cat "$T/emit2.err"; exit 1; }
cat > "$T/treiber.c" <<'CEOF'
#include <stdio.h>
#include <string.h>
#include "ring.c"
#ifdef MIT_BINDUNG
#include "linux_bind.c"
#endif
static long rss_kib(void)
{
    long a = 0, b = 0;
    FILE *f = fopen("/proc/self/statm", "r");
    if (f == NULL || fscanf(f, "%ld %ld", &a, &b) != 2) {
        return -1;
    }
    fclose(f);
    return b * (long)(sysconf(_SC_PAGESIZE) / 1024);
}
int main(void)
{
    long voll, danach;
    unsigned long k, nichtnull = 0;
    memset(RING, 0xAB, sizeof RING);
    voll = rss_kib();
#ifndef OHNE_GABEN
    freigeben();
#endif
    danach = rss_kib();
    for (k = 0; k < sizeof RING; k++) {
        nichtnull += RING[k] != 0;
    }
    printf("%ld %ld %lu\n", voll, danach, nichtnull);
    return 0;
}
CEOF
sed -i '1i #include <unistd.h>' "$T/treiber.c"
build() { # name flags...
    local n=$1; shift
    cc -O1 -Wall -Wextra -I"$T" "$@" -o "$T/$n" "$T/treiber.c" 2> "$T/$n.err" || { echo "RED: $n did not build"; cat "$T/$n.err"; exit 1; }
}
build mit -DMIT_BINDUNG
build ohne
build gift -DMIT_BINDUNG -DOHNE_GABEN
read -r v1 d1 z1 < <("$T/mit")
read -r v2 d2 z2 < <("$T/ohne")
read -r v3 d3 z3 < <("$T/gift")
echo "bound   : rss ${v1} -> ${d1} KiB, non-zero bytes ${z1}"
echo "unbound : rss ${v2} -> ${d2} KiB, non-zero bytes ${z2}"
echo "poison  : rss ${v3} -> ${d3} KiB, non-zero bytes ${z3}"
# (1) at least 3/4 of 1024 KiB left the resident set, and every byte is zero
[ "$z1" -eq 0 ] && [ $((v1 - d1)) -ge 768 ] || { echo "RED: bound run kept its pages or its bytes"; fail=1; }
# (2) the emitted loop alone: zero, and the pages stay (the binding is what returns them)
[ "$z2" -eq 0 ] && [ $((v2 - d2)) -lt 256 ] || { echo "RED: unbound run neither zeroed nor stayed resident as designed"; fail=1; }
# (3) the poison build must FAIL the criterion of (1)
if [ "$z3" -eq 0 ] && [ $((v3 - d3)) -ge 768 ]; then echo "RED: the poison passed -- the test cannot see a missing give-back"; fail=1; fi
[ "$fail" -eq 0 ] && echo "GREEN: pages given back by the binding, zeroes kept without it, the poison caught"
exit $fail
