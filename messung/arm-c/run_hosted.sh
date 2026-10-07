#!/bin/bash
# usage: run_hosted.sh GABBRO_BIN OUTDIR [LINUX_GAB]   (run from the worktree root)
# The three hosted drivers of instrumente/pruefe-emission.sh that need the OS binding
# (158 arena commit, 175-gebunden page return, 159 threads), with the binding
# bibliothek/linux/linux-aarch64.gab, cross-compiled and run under qemu-aarch64.
# Expected (the x86 harness): 118 / 7 / 64.
BIN=$1; OUT=$2; LIN=${3:-bibliothek/linux/linux-aarch64.gab}
mkdir -p "$OUT"
CC="aarch64-linux-gnu-gcc -static -std=c11 -Wall -Wextra -Werror -I$OUT -Ilaufzeit"
"$BIN" emit "$LIN" > "$OUT/linux_bind.c" || exit 1
"$BIN" runtime arena > "$OUT/arena_laufzeit.c" || exit 1
"$BIN" runtime threads > "$OUT/faden_laufzeit.c" || exit 1
"$BIN" emit beispiele/158-arena-commit.gab > "$OUT/b158.c" || exit 1
"$BIN" emit beispiele/175-puffer-gibt-seiten-zurueck.gab > "$OUT/b175.c" || exit 1
"$BIN" emit beispiele/159-laufzeit-start.gab > "$OUT/b159.c" || exit 1
cat > "$OUT/d158.c" <<'EOF'
#include <stdio.h>
#include "b158.c"
#include "arena_laufzeit.c"
#include "linux_bind.c"
int main(void) {
    gabbro_arena_reserve(&Vorrat_desc);
    printf("%u\n", fuellen());
    return 0;
}
EOF
cat > "$OUT/d175.c" <<'EOF'
#include <stdio.h>
#include "b175.c"
#include "linux_bind.c"
int main(void) {
    printf("%u\n", geben());
    return 0;
}
EOF
cat > "$OUT/d159.c" <<'EOF'
#include <stdatomic.h>
#include <stdio.h>
#include "b159.c"
#include "faden_laufzeit.c"
static _Atomic int sperre_L = 0;
void L_nimm(void) { while (atomic_exchange_explicit(&sperre_L, 1, memory_order_acquire)) { } }
void L_gib(void) { atomic_store_explicit(&sperre_L, 0, memory_order_release); }
int main(void) {
    printf("%u\n", lauf());
    return 0;
}
EOF
for n in 158 175 159; do
  for o in -O0 -O2; do
    extra=""
    [ $n = 159 ] && extra="$OUT/linux_bind.c"
    if $CC $o -o "$OUT/h$n$o" "$OUT/d$n.c" $extra 2> "$OUT/h$n$o.cc"; then
      echo "== $n $o: $(timeout 20 qemu-aarch64 "$OUT/h$n$o" 2>&1 | tr '\n' ' ')"
    else
      echo "== $n $o: COMPILE FAIL (see $OUT/h$n$o.cc)"
    fi
  done
done
