# MUSE-REPORT-247 — Ticket lock through the chain: check, emit, compile, RUN

Lane 247 (TODO §0 threading, MUST). Diff of this lane: this report only.
`laufzeit/sperre.gab` is byte-identical to master (no repair needed, none
applied); no file under `beispiele/`, `crates/`, `grammatik/` or
`instrumente/` touched. Driver and logs below live in lane scratch
(`.tmp/247/`, git-ignored, not committed); the run log is quoted verbatim
in §5 so the evidence travels with the report.

## 0. Verdict up front

- `gabbro pruefe laufzeit/sperre.gab`: **0 errors**, 2 hints (both `E247`,
  §6 F-247-1). Unchanged from lane 201's measurement.
- `gabbro emit laufzeit/sperre.gab`: exit 0, 75 lines of C.
- Emitted C under guardian flags `cc -std=c11 -Wall -Wextra -Werror -c`:
  **CLEAN at -O0 and -O2, under both `cc` (gcc 13.3.0) and `clang` (18.1.3)**.
- Hosted RUN, two threads hammering one plain counter under the Gabbro
  lock (`nimm`/`gib`), 200000 iterations each: **result == expected
  (400000 == 400000), fail-stop exit never fired, exit 0** — with the `cc`
  and the `clang` build, plus a ThreadSanitizer build with zero warnings.
- Sensitivity (the oracle bites): the SAME driver with the lock compiled
  out (`-D OHNE_SPERRE`) trips
  `WARNING: ThreadSanitizer: data race` on the counter and exits 66.
- Stress finding (§6 F-247-2): at higher contention (4x500k, 8x200k,
  8x1M) the draw bound (`bounded 64 ops` CAS loop) FIRES and the thread
  stops (SIGABRT via `warte_aufgegeben`). Safe direction (no duplicated
  ticket, never an unserved hold), but a measured liveness cliff.
- `./cargo-pruef`: `== exit 0; failing tests: 0` (50 `test result: ok`
  lines, 0 `FAILED`). Corpus verdict diff: zero. MARKE_EMIT delta: zero
  (all six marks unchanged, §7).

## 1. Chain measurements (all re-run on 2026-09-17, fisch)

```
$ ./target/debug/gabbro pruefe laufzeit/sperre.gab
hint: [E247] laufzeit/sperre.gab:70:19: `NOW` is read by the body of `gib` ...
hint: [E247] laufzeit/sperre.gab:52:20: `NEXT` is read by the body of `nimm` ...
laufzeit/sperre.gab: 7 items, 0 errors, 2 hints

$ ./target/debug/gabbro emit laufzeit/sperre.gab > .tmp/247/sperre.c
emit exit 0   (75 lines, empty stderr)

$ cc    -std=c11 -O0/-O2 -Wall -Wextra -Werror -c -o /dev/null sperre.c  CLEAN
$ clang -std=c11 -O0/-O2 -Wall -Wextra -Werror -c -o /dev/null sperre.c  CLEAN
```

Link + run (driver §4, barrier-started threads, plain `unsigned` counter):

```
$ cc    ... -O2 -pthread -o treiber247-cc treiber247.c     # link OK
$ clang ... -O2 -pthread -o treiber247-clang treiber247.c  # link OK
$ ./treiber247-cc    2 200000
treiber247: faden=2 iters=200000 zaehler=400000 erwartet=400000 aufgegeben=0
exit 0 (run 3x, identical)
$ ./treiber247-clang 2 200000
treiber247: faden=2 iters=200000 zaehler=400000 erwartet=400000 aufgegeben=0
exit 0
```

## 2. Instruction table — `CTicket.lean` (`TSchritt`) vs the emitted C

Model C (CTicket.lean header): `my = fetch_add(&L.next, relaxed)`;
`while (load_acquire(&L.now) != my) ;`; `n = load_relaxed(&L.now)`;
`store_release(&L.now, n+1)`. Gabbro sites: `nimm` (CAS draw + spin),
`gib` (load + store), helper `folge`.

| # | CTicket instruction | Emitted C | Verdict |
|---|---|---|---|
| 1 | `zieht`: `my = atomic_fetch_add_explicit(&L.next, 1u, relaxed)` — one step, never fails | `nimm`: `load_relaxed(NEXT)` + `folge` + `compare_exchange_weak_relaxed` loop, max 64 passes, then `_Noreturn warte_aufgegeben()` | NAMED DEVIATION D1. No fetch-add arm in the emitter (lane 201 F2; TODO §-1 lane 221 owns the arm). Orderings match (relaxed/relaxed), wrap matches (mod 2^32 via `folge`). New failure mode: after 64 lost races the thread STOPS instead of drawing — fail-stop, no duplicated ticket, but the C primitive's wait-freedom is gone. Bound 64 is a writer's choice, not derived. Fires under contention: §6 F-247-2. |
| 2 | `dreht`: `load_acquire(&L.now) != my`, NOTHING changes | `nimm`: counted `for` with empty body over `!(atomic_load_explicit(&NOW, acquire) == my)`, bound 1431655765 passes (= 4294967295 ops / 3 per pass) + post-loop recheck calling `warte_aufgegeben()` | MATCHES, with a bound (D2). Load ordering acquire as modelled. Overrun stops instead of spinning forever — fail-stop again. Never observed to fire (§5). |
| 3 | `tritt`: load finds `now == my` — `L_nimm` RETURNS, caller becomes holder | Loop exit, fall out of `nimm` (holder = program position after return, as in the model) | MATCHES, under the same bound as (2). |
| 4 | `gibt`: release store `now+1` (Lean rule: ONE store; trust-base C: load+store) | `gib`: `n = atomic_load_explicit(&NOW, acquire); atomic_store_explicit(&NOW, folge(n), release)` | MATCHES the trust-base C (load+store), DIFFERS from the one-store Lean rule by the extra load (D3a). Load ordering acquire where trust base uses relaxed (D3b) — stronger, harmless here: no payload rides on it (`publishes nothing`). Load+store non-atomic as a pair, exactly as in the trust base; safe under holder exclusion. |

Structural deviations: two separate globals `NEXT`/`NOW` vs one struct
`L_wort` (D4, same semantics); `u32` wrap IMPLEMENTED via `folge` where the
model cuts it away at `Nat` (D5 — the Gabbro side says more, in the safe
direction); `static nimm/gib` vs external `L_nimm/L_gib` (D6, linkage);
`folge` helper, both pass counters, both fail-stop exits, `NOW_ORDER`
define (extras with no model counterpart). Nothing is missing: all four
instructions are present. The guard finding `gib_ohne_wache` transfers
unchanged: `gib` performs no holder check — in the hosted run the driver
calls it only as holder; the checker-side discipline (emit `gib` only
where the holder stands) is future work, same as for the trust base.

## 3. Oracle pair — ThreadSanitizer at the required shape (2x200000)

```
$ cc ... -fsanitize=thread -o treiber247-tsan treiber247.c
$ ./treiber247-tsan 2 200000
treiber247: faden=2 iters=200000 zaehler=400000 erwartet=400000 aufgegeben=0
exit 0, NO ThreadSanitizer output (silent)

$ cc ... -fsanitize=thread -DOHNE_SPERRE -o treiber247-tsan-offen treiber247.c
$ ./treiber247-tsan-offen 2 200000
WARNING: ThreadSanitizer: data race (pid=...)
  Read of size 4 ... by thread T1:  #0 hammern ...
  Previous write of size 4 ... by thread T2:  #0 hammern ...
  Location is global 'zaehler' ...
ThreadSanitizer: reported 1 warnings
exit 66
```

The counter is deliberately PLAIN (`static unsigned zaehler`), so only the
lock stands between the threads and a warning. Same program, lock removed:
the detector fires. Sensitivity proven at the exact required
configuration. (Count note: even unlocked, the final count came out exact
— a single `add` has a sub-nanosecond race window, so counts alone cannot
bite here; that is why the race detector is the oracle, as the task
permits. The driver comment claiming the control "must lose counts" is
overstated — corrected here: it must trip TSan, and it does.)

## 4. Stress runs — the draw bound fires (measured 2026-09-17)

```
$ ./treiber247-cc 8 1000000        -> warte_aufgegeben FIRED, Aborted (134)
$ ./treiber247-cc 4 500000         -> warte_aufgegeben FIRED, Aborted (134)
$ ./treiber247-cc 8 200000         -> warte_aufgegeben FIRED, Aborted (134, 3/3)
$ ./treiber247-clang 8 200000      -> zaehler=1600000 erwartet=1600000 aufgegeben=0, exit 0 (3/3)
```

Diagnostic build (copy of the emitted C with one marker per fail-stop
site, scratch only): 8x1M and 4x500k both print
`DRAW bound (64 CAS passes) FIRED` — it is the ticket-draw CAS loop
(`bounded 64 ops`), never the spin bound, that trips. Overlap control on
this 16-core machine: 8/8 threads simultaneously inside (measured), so
contention is real, not an artefact of serialised threads. Machine load
during runs ~2-4 (other lanes' test slots), which moves the exact
threshold but not the fact: the cc build trips at 8x200k 3/3 while the
clang build (same source, different codegen/timing) passes 3/3.

## 5. Full run log (verbatim, required shape + oracle + stress)

```
treiber247: faden=2 iters=200000 zaehler=400000 erwartet=400000 aufgegeben=0   # cc x3
treiber247: faden=2 iters=200000 zaehler=400000 erwartet=400000 aufgegeben=0   # clang
treiber247: faden=2 iters=200000 zaehler=400000 erwartet=400000 aufgegeben=0   # TSan-lock, no warnings
WARNING: ThreadSanitizer: data race ... Location is global 'zaehler' ...      # TSan-no-lock, exit 66
treiber247: warte_aufgegeben FIRED -- a bound was hit                         # cc 4x500k/8x200k/8x1M
treiber247: faden=8 iters=200000 zaehler=1600000 erwartet=1600000 aufgegeben=0 # clang 8x200k x3
```

## 6. Findings for the owner

- F-247-1 (checker, standing hint, NOT routed around): the 2x `E247`
  (`NEXT`/`NOW` read with no `Held(L)` guard while some function writes
  them) cannot be silenced honestly. A lock guarding the lock's own
  counters is an infinite regress — atomics are the base case of the guard
  discipline — and the footprint rule has no atomic exemption. Calibration:
  EVERY lock-free atomic precedent in the corpus carries the identical
  hints (`beispiele/35-tausch.gab`, `-117-`, `-140-`, all 0 errors + 2
  hints). So "0 errors, 0 hints" is unachievable for this file without
  weakening it (a circular `requires Held`) or changing the checker (out
  of scope: NOT checker passes). Deliverable "0 errors" holds; "0 hints"
  is refused by finding, as §0 prescribes. No repair applied to
  `sperre.gab` — the file is byte-identical to master.
- F-247-2 (liveness cliff, measured): `bounded 64 ops` on the draw CAS
  loop fires at >=4 hammer threads (cc build). Fail-stop is the safe
  direction (never a duplicated ticket — Finding 2 of CTicket as a
  program is still avoided), but the bound is a writer's number, and under
  contention it is a wall, not a rarity. This is measured input to the
  TODO §-1 decision gate: whether `emit.rs` gains an `atomic_fetch_add`
  arm (lane 221) decides whether D1/F-247-2 disappear or stay carried as
  named premises of the correspondence proof.
- F-247-3 (configuration sensitivity): the cliff is timing-sensitive —
  clang passes exactly the shape cc aborts on (8x200k, 3/3 each). Any
  future regression bound on this lock must pin compiler + shape, not
  just the `.gab` file.
- F-247-4 (test-design trap, avoided): single-`add` critical sections do
  not lose counts even fully parallel and unlocked (sub-ns race window;
  overlap 8/8 proven). A stress-count oracle on this shape would be
  vacuous — the race detector is the load-bearing oracle. Future hosted
  lock tests should either widen the critical section or (as here) rely
  on TSan, never on counts alone.

## 7. Marks, corpus, test suite — all zero-delta

- MARKE_EMIT delta: none. Read off `instrumente/pruefe-emission.sh`:
  `MARKE_EMIT=117`, `MARKE_EMIT_G=18`, `MARKE_EMIT_M=143`,
  `MARKE_EMIT_N=2`, `MARKE_EMIT_P=1`, `MARKE_EMIT_L=1`,
  `MARKE_EMIT_X=0` — untouched by this lane (not allowed to touch them),
  and no re-measurement was needed: `sperre.gab` still emits (exit 0),
  so the `L=1` ratchet still holds.
- Corpus verdict diff: zero. No existing file changed (`git diff
  master --stat` before this report: empty); the only added file is this
  report, which no guardian reads.
- `./cargo-pruef` (2026-09-17, full queued run):
  `== exit 0; failing tests: 0` — 50 `test result: ok` lines, 0 `FAILED`,
  0 non-ok. Last log line: `test result: ok. 0 passed; 0 failed;
  0 ignored; 0 measured; 0 filtered out` (gabbro_syntax doc-tests).
- `./lean-bau`: not run — no `grammatik/` change exists (nothing to
  build). `emit.rs` untouched; no `C001` named (no lowering missing:
  every construct in the lock lowers today).

## 8. What remains open (not this lane)

- The 0-hint gap (F-247-1) needs a checker-side atomic/base-case
  exemption — a language decision, not a lock repair.
- The draw-bound cliff (F-247-2) needs the fetch-add decision (lane 221
  gate) or a derived bound + progress assumption in the proof.
- Thread start / idle root / `main` (TODO §0 items 2-3): this lane ran a
  C driver, not an emitted one; A4 is still an assumption.
- A second concurrent program through the executed set (TODO §0 item 3)
  is still open; this lane executed the runtime, not a program.

## 9. Reproduction (driver source, scratch `.tmp/247/treiber247.c`)

Build from the tree root (emitted file as include, as in
`laufzeit/start.c`'s `EINHEIT_INCLUDE` pattern):

```
./target/debug/gabbro emit laufzeit/sperre.gab > .tmp/247/sperre.c
cd .tmp/247
cc -std=c11 -O2 -Wall -Wextra -Werror -pthread -o t-cc treiber247.c
./t-cc 2 200000            # expect exact count, aufgegeben=0, exit 0
cc ... -fsanitize=thread -o t-tsan treiber247.c && ./t-tsan 2 200000
cc ... -fsanitize=thread -DOHNE_SPERRE -o t-offen treiber247.c && ./t-offen 2 200000
```

```c
#define _POSIX_C_SOURCE 200809L /* pthread_barrier under -std=c11 */
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include "sperre.c"              /* Gabbro-emitted nimm/gib/folge, NEXT/NOW */
#ifdef OHNE_SPERRE               /* sensitivity control: empty lock */
#undef nimm
#undef gib
#define nimm() ((void)0)
#define gib() ((void)0)
#endif
static _Atomic unsigned aufgegeben = 0;
_Noreturn void warte_aufgegeben(void) {
    atomic_fetch_add_explicit(&aufgegeben, 1u, memory_order_relaxed);
    fprintf(stderr, "treiber247: warte_aufgegeben FIRED -- a bound was hit\n");
    abort();
}
static unsigned zaehler = 0;     /* PLAIN on purpose: TSan sees every miss */
static pthread_barrier_t startschranke;   /* all threads start together */
static void *hammern(void *arg) {
    unsigned iters = *(unsigned *)arg;
    pthread_barrier_wait(&startschranke);
    for (unsigned i = 0; i < iters; i++) { nimm(); zaehler += 1; gib(); }
    return NULL;
}
static int lauf(unsigned faden, unsigned iters) {
    zaehler = 0;
    pthread_t *t = malloc(sizeof(*t) * faden);
    if (!t) return 2;
    pthread_barrier_init(&startschranke, NULL, faden);
    for (unsigned k = 0; k < faden; k++) pthread_create(&t[k], NULL, hammern, &iters);
    for (unsigned k = 0; k < faden; k++) pthread_join(t[k], NULL);
    pthread_barrier_destroy(&startschranke);
    free(t);
    unsigned erwartet = faden * iters;
    unsigned gab_auf = atomic_load_explicit(&aufgegeben, memory_order_relaxed);
    printf("treiber247: faden=%u iters=%u zaehler=%u erwartet=%u aufgegeben=%u\n",
           faden, iters, zaehler, erwartet, gab_auf);
    return (zaehler == erwartet && gab_auf == 0) ? 0 : 1;
}
int main(int argc, char **argv) {
    unsigned faden = 2, iters = 200000;
    if (argc > 1) faden = (unsigned)strtoul(argv[1], NULL, 10);
    if (argc > 2) iters = (unsigned)strtoul(argv[2], NULL, 10);
    return lauf(faden, iters);
}
```
