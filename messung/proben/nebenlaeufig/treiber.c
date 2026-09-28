/* messung/proben/nebenlaeufig/treiber.c -- ONE driver for TWO implementations
 * of `sperre-rueckgabe.gab` (server lane, TODO section 0e, acceptance point 2).
 *
 * The same driver is compiled twice: once over the EMITTED C of the probe
 * (`gabbro emit`) and once over the HANDWRITTEN C version beside it
 * (`sperre-rueckgabe-hand.c`). Both binaries must print the same first line.
 * That is what makes this a differential test and not a demonstration: the
 * handwritten side was written from the SOURCE, not from the emitted file, so
 * an agreement is a statement about the lowering.
 *
 * WHAT THIS FILE PROVIDES, AND WHY IT MEASURES MORE THAN AN ANSWER
 * ---------------------------------------------------------------
 *   * `L_nimm` / `L_gib` -- the lock the unit names. A test-only spinlock: the
 *     emitter writes the two prototypes and no body, because the primitive is a
 *     trust base and not a product (MESSUNGEN.md section 2). Beside the lock the
 *     driver counts two things:
 *       - `genommen`: how often the lock was taken. That number is part of the
 *         compared line, so the lock DISCIPLINE is compared, not only the answer.
 *       - `gestossen`: how often a taker found the lock already held. That is the
 *         OVERLAP WITNESS: a run of two threads that never contend has measured
 *         a sequential execution, and a sequential run of a concurrent program
 *         proves nothing about concurrency. Zero overlap is a finding, not a
 *         pass (and the instrument's gift 3 is exactly a sequential twin).
 *   * `bremse()` -- a busy delay, spelled twice and for two different reasons:
 *       - INSIDE the section (after the acquire): two threads that both hold the
 *         lock for a while really do contend, so the overlap witness above sees
 *         something on every schedule instead of once in a hundred runs.
 *       - AFTER the release: it widens the window between a release and anything
 *         that still reads the protected carrier. *It does not create that
 *         window.* A read lowered outside the section is outside it with or
 *         without this delay; the delay only decides whether a run can SEE it.
 *
 * The delay is a volatile loop and not `nanosleep`: no libc threading, no
 * syscall, nothing that could itself synchronise the two threads and hide what
 * is being measured. `GABBRO_BREMSE` is the iteration count, handed in with -D.
 *
 * Output, two lines:
 *     <answer> <lock acquisitions>      -- deterministic; compared between the two
 *     overlap <contended acquisitions>  -- schedule-dependent; must not be 0
 */
#include <stdint.h>
#include <stdio.h>
#include <stdatomic.h>

#ifndef GABBRO_BREMSE
#define GABBRO_BREMSE 20000u
#endif

static _Atomic int sperre_L = 0;
static _Atomic unsigned genommen = 0;
static _Atomic unsigned gestossen = 0;

static void bremse(void)
{
    for (volatile unsigned i = 0; i < (unsigned)GABBRO_BREMSE; i++) {
    }
}

void L_nimm(void);
void L_gib(void);

void L_nimm(void)
{
    int erster = 1;
    while (atomic_exchange_explicit(&sperre_L, 1, memory_order_acquire)) {
        if (erster) {
            atomic_fetch_add_explicit(&gestossen, 1u, memory_order_relaxed);
            erster = 0;
        }
    }
    atomic_fetch_add_explicit(&genommen, 1u, memory_order_relaxed);
    bremse();
}

void L_gib(void)
{
    atomic_store_explicit(&sperre_L, 0, memory_order_release);
    bremse();
}

#include "@ERZEUGT@"
#include "@FADEN@"

int main(void)
{
    uint32_t antwort = lauf();
    printf("%u %u\n", (unsigned)antwort,
           (unsigned)atomic_load_explicit(&genommen, memory_order_relaxed));
    printf("overlap %u\n",
           (unsigned)atomic_load_explicit(&gestossen, memory_order_relaxed));
    return 0;
}
