# MUSE-REPORT-201 — the ticket lock in Gabbro itself (runtime, part 1)

Lane 201. Diff: `laufzeit/sperre.gab` (new) plus this report. Nothing in
`beispiele/`, `crates/`, `grammatik/` or `instrumente/` touched.

## 0. Verdict up front

**Accepted.** `gabbro pruefe laufzeit/sperre.gab`: 7 items, **0 errors**,
2 hints (both `E247`, see §1). `gabbro emit`: rc=0, C written.
`cc -std=c11 -Wall -Wextra -Werror -c` clean at **-O0 and -O2**.
No checker, emitter, grammar or rule was changed to get there.

## 1. Refusal list (checker and emitter, with codes)

Checker refusals met on the way, all resolved WITHOUT touching the
language — each fix stayed inside the `.gab` file:

1. `[K001]` — `nimm` promised `<= 4294967296 ops`, body costs 4294967298
   (the `retry` bound plus two). Fixed by promising the computed number
   (`<= 4294967299 ops` after the `folge` call added one more). The number
   is the static computation, not a negotiation.
2. `[C001]` (emitter) — `exchange update(t)` without
   `bounded … ops on_exceeded …`. The emitter lowers EVERY update body to
   a bounded CAS loop and refuses the clauses' absence by name, even for
   the primitive `t+1` shape that `SPRACHE.md` says would be
   `atomic_fetch_*`. Fixed by writing the construct's own clauses
   (`bounded 64 ops on_exceeded warte_aufgegeben`). Consequence: there is
   **no `atomic_fetch_add` in the emitted C** (the string occurs only in a
   comment in `emit.rs`) — see `zieht` in §2.
3. `[C001]` (emitter, twice) — wrapping `+%` over operands whose exact
   ranges "cannot be read off their declarations": once over the `let`
   local `n`, once over the `exchange` binder `t`. The emitter's
   `wrap_side`/`ort_typ` resolve bare names only through statics/params,
   never locals or binders. Fixed by moving the wrap into a helper
   `folge(x : u32) -> u32` whose PARAMETER resolves to the full word, and
   calling it from both sites (`return folge(t);`, `NOW = folge(n) …`).
   Emitted as `(uint32_t)(((uint32_t)(x) + (uint32_t)(1)))` — C unsigned
   arithmetic, modulo 2^32, same as the trust-base `unsigned`.

Standing hints (NOT refusals, NOT routed around):

- `2 × [E247]` — `NEXT`/`NOW` are read with no signature lock held while
  some function writes them; "every written carrier wants a
  `requires Held(L)` guard". A lock protecting the lock's own counters is
  an infinite regress — atomics are the base case of the guard discipline
  (`SYNTAX.md` §11: unguarded shared access ordered by the memory model).
  Calibration: the accepted corpus file
  `beispiele/116-payload-free-counter.gab` carries the identical hint on
  its bare atomic read. Nothing to fix.

## 2. Instruction table — `CTicket.lean` vs the emitted C

`CTicket.lean` (`TSchritt`): `zieht` (fetch_add draw), `dreht` (failed spin
load, no state change), `tritt` (successful spin load, acquire completes),
`gibt` (release store). Order below is that order.

| # | CTicket instruction | Emitted C (`nimm`/`gib`/`folge`) | Verdict |
|---|---|---|---|
| 1 | `zieht`: `my = atomic_fetch_add_explicit(&L.next, 1u, relaxed)` — ONE SC step, never fails | `nimm` lines 44–61: `load_relaxed(NEXT)` + `folge` + `compare_exchange_weak_relaxed` in a `for(;;)`, max 64 passes, then `_Noreturn warte_aufgegeben()` | DIFFERS. No fetch-add arm exists in the emitter; the draw is a bounded CAS loop (orderings match: relaxed/relaxed; wrap matches: mod 2^32). New failure mode: after 64 lost races the thread stops instead of drawing — fail-stop, so no duplicated ticket, but the C primitive's wait-freedom is gone. Bound `64` is my choice, not derived. |
| 2 | `dreht`: `load_acquire(&L.now) != my`, NOTHING changes | `nimm` line 64: counted `for` with empty body over `!(atomic_load_explicit(&NOW, memory_order_acquire) == my)` | MATCHES, with a bound. Load ordering acquire — as modelled. Extra: pass counter `_r1 < 1431655765u` (= 4294967295/3, i.e. the op bound ÷ 3 ops per pass) plus post-loop recheck (line 66). |
| 3 | `tritt`: `load_acquire(&L.now) == my` — `L_nimm` RETURNS, caller becomes holder | loop exit at line 64/66, fall out of `nimm` (holder = program position after return, as in the model) | MATCHES, with the same bound as (2). Overrun calls `warte_aufgegeben()` instead of spinning forever — fail-stop again (line 66). |
| 4 | `gibt`: `atomic_store(&L.now, now+1, release)` — ONE store | `gib` lines 70–74: `n = atomic_load_explicit(&NOW, memory_order_acquire); atomic_store_explicit(&NOW, folge(n), memory_order_release)` | MATCHES the trust-base C (which is also load+store), DIFFERS from the one-store Lean rule by the extra load. Load ordering is acquire where the trust base uses relaxed — stronger, harmless here (no payload rides on it; `publishes nothing`). Load+store is non-atomic as a pair, exactly as in the trust base; under holder exclusion no one else stores concurrently. |

Nothing is missing: all four instructions are present. Extra in the C
that the model has no counterpart for: `folge` helper, both pass counters,
both fail-stop exits, the `NOW_ORDER` define, `static … __attribute__((unused))`
on `nimm`/`gib` (TODO §0's shape: static roots nobody calls, no `main` —
expected for a runtime module; the driver that calls them is TODO §0 item 2,
a later lane).

Ordering map used (read off `emit.rs`, not assumed): a declaration names the
STORE side; the load side is derived — `acquire`/`release` decls both give
(store release, load acquire). Hence `atomic NOW : u32 acquire` yields
exactly spin-acquire + release-store. `NEXT` (`relaxed`) yields
relaxed/relaxed. The full C declares `_Atomic uint32_t` for both.

## 3. Exact C produced (`gabbro emit laufzeit/sperre.gab`, 74 lines)

```c
_Atomic uint32_t NEXT;

/* awaits under A10 (release_stellt_sichtbarkeit_her, UNFALSIFIABLE):
 * the ordering below is the one the source declared, not C's default.
 * payload: nothing */
_Atomic uint32_t NOW;
#define NOW_ORDER memory_order_acquire

static uint32_t folge(uint32_t x) __attribute__((const)) __attribute__((unused));

_Noreturn void warte_aufgegeben(void);

static void nimm(void) __attribute__((unused));

static void gib(void) __attribute__((unused));

static uint32_t folge(uint32_t x) {
    return (uint32_t)(((uint32_t)(x) + (uint32_t)(1)));
}

static void nimm(void) {
    /* NEXT exchange update(t) -- a bounded CAS loop, and bounded is
     * the point: SPRACHE.md forbids an unbounded one. The body computes
     * old -> new and is pure, so re-running it on a lost race is free of
     * consequence. `warte_aufgegeben` is the exit at 64 passes. */
    uint32_t my;
    {
        uint32_t _ci1 = 0;
        uint32_t _cx1 = atomic_load_explicit(&NEXT, memory_order_relaxed);
        for (;;) {
            uint32_t _cn1;
            {
                const uint32_t t = _cx1;
                _cn1 = folge(t); goto _cn1_fertig;
                _cn1_fertig: ;
            }
            if (atomic_compare_exchange_weak_explicit(
                    &NEXT, &_cx1, _cn1, memory_order_relaxed, memory_order_relaxed)) break;
            if (_ci1 >= (uint32_t)(64)) { warte_aufgegeben(); }
            _ci1++;
        }
        my = _cx1;
    }
    {
        uint32_t _r1 = 0;
        for (; !(atomic_load_explicit(&NOW, memory_order_acquire) == my) && _r1 < 1431655765u; _r1 += 1) {
        }
        if (_r1 >= 1431655765u && !(atomic_load_explicit(&NOW, memory_order_acquire) == my)) { warte_aufgegeben(); }
    }
}

static void gib(void) {
    uint32_t n = atomic_load_explicit(&NOW, memory_order_acquire);
    /* publishes { nothing } -- paired at compile time (V001-V004) */
    atomic_store_explicit(&NOW, folge(n), memory_order_release);
}
```

(Preamle: license header, `#include <stdint.h> <stdbool.h> <stdatomic.h>
<math.h>`, two `_Static_assert` prelude pins — byte-identical to every unit.)

Compile: `cc -std=c11 -Wall -Wextra -Werror -c` → clean at -O0 and -O2
(object files only; linking is not attempted — `warte_aufgegeben` is
declared `_Noreturn` without a definition and there is no `main`, both by
design: the driver supplies them).

## 4. What was done, names

- `laufzeit/sperre.gab`, module `laufzeit::sperre`: atomics `NEXT`
  (`relaxed`), `NOW` (`acquire`); `impl fn folge`, `impl fn nimm`,
  `impl fn gib`; `extern fn warte_aufgegeben() -> never`.
- No Lean, no Rust, no new diagnostics, no witness needed (task names no
  `ZEUGE:` target and forbids touching `grammatik/`).

## 5. What I did NOT measure (for the correspondence lane)

- Nothing proved: no refinement, no invariant, no simulation. The table in
  §2 is read off the two texts, not a theorem.
- Never run: no driver, no threads, no contention. The CAS bound (64) and
  the spin bound (4294967295 ops → 1431655765 passes) are unvalidated
  numbers; liveness under them is not shown.
- No disassembly/machine-shape check (`SYNTAX.md` §11 per-form atomicity
  table); only `cc` acceptance at -O0/-O2 on x86_64, gcc 13.3.0.
- No `-O1`, no other arch, no `main`-linked binary.
- `./cargo-pruef` (queued build+test) was still running behind other lanes'
  slots when this report was written; it cannot be affected by this diff
  (no test or guardian reads `laufzeit/` — `beispiele.rs`/`korpus.rs` walk
  `beispiele/` only, `pruefe-emission.sh` names files individually).
  `./lean-bau` untouched (no `grammatik/` change).

## 6. Findings for the owner

1. The lock CAN be written in Gabbro and passes the checker with 0 errors.
   The language expresses its own runtime's ticket lock — modulo §2's
   `zieht` difference.
2. The one structural gap: the emitter has NO `atomic_fetch_*` arm although
   `SPRACHE.md` promises one for primitive update bodies. Every ticket draw
   is a CAS loop with a writer-chosen bound. Either the doc or the emitter
   should move.
3. `+%` is checker-clean but emitter-blind over locals and `exchange`
   binders; only params/statics carry a readable range. The `folge` helper
   is a workaround for a reader that could look one binder deeper.
4. Both differences point the same way: bounded + fail-stop where the C is
   unbounded. That is the safe direction (never a duplicated ticket, never
   a lock held without a served ticket), but it is NOT the same program:
   after 64 lost CAS races or 1431655765 unsuccessful spin passes the
   thread stops. The correspondence proof must carry these two bounds as
   named premises — or the emitter gains a fetch-add arm and the spin a
   `progress` assumption (the `forever … progress` shape exists for exactly
   this: the releaser's store as the named environment contribution).
