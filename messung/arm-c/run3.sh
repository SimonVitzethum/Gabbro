#!/bin/bash
# usage: run3.sh OUTDIR   (run from the worktree root; OUTDIR is the units.sh output)
# Links the emitted aarch64 C of beispiele/74, 90, 96 against the SAME drivers
# instrumente/pruefe-emission.sh uses (TREIBER74/90/96, copied here), runs them under
# qemu-aarch64 at -O0 and -O2 and prints the output next to the expected one.
# Poison probe: the `svc #0` replaced by `nop` must change the output.
D=$1
cat > "$D/drv74.c" <<'EOF'
#include <stdio.h>
#include "74-syscall-schreiben.c"
int main(void) {
    static const char msg[3] = {'o', 'k', '\n'};
    uint64_t n = schreibe(1, (uint64_t)msg, 3);
    printf("%llu\n", (unsigned long long)n);
    return 0;
}
EOF
cat > "$D/drv90.c" <<'EOF'
#include <stdio.h>
#include "90-syscall-errno.c"
int main(void) {
    static const char msg[3] = {'o', 'k', '\n'};
    uint64_t n = schreibe_ungueltig((uint64_t)msg, 3);
    printf("%llu\n", (unsigned long long)n);
    return 0;
}
EOF
cat > "$D/drv96.c" <<'EOF'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include "96-buffered-writer.c"
void writer_hangs(void) { fprintf(stderr, "writer_hangs: overrun\n"); abort(); }
int main(void) {
    uint64_t n = writer_demo(1);
    printf("%llu\n", (unsigned long long)n);
    return 0;
}
EOF
for n in 74 90 96; do
  for o in -O0 -O2; do
    aarch64-linux-gnu-gcc -static -std=c11 -Wall -Wextra -Werror $o -Ilaufzeit -I"$D" \
        -o "$D/drv$n$o" "$D/drv$n.c" 2> "$D/drv$n$o.cc" || { echo "$n $o COMPILE FAIL"; continue; }
    echo "== $n $o: $(qemu-aarch64 "$D/drv$n$o" | tr '\n' ' ')"
  done
done
# poison: svc #0 -> nop in the emitted C of 74
sed 's/"svc #0\\n"/"nop\\n"/' "$D/74-syscall-schreiben.c" > "$D/74-gift.c"
sed 's/74-syscall-schreiben.c/74-gift.c/' "$D/drv74.c" > "$D/drv74g.c"
aarch64-linux-gnu-gcc -static -std=c11 -O2 -Ilaufzeit -I"$D" -o "$D/drv74g" "$D/drv74g.c" &&
    echo "== 74 poison (nop for svc): $(qemu-aarch64 "$D/drv74g" | tr '\n' ' ')"
