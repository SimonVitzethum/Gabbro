/* messung/proben/nebenlaeufig/sperre-rueckgabe-hand.c -- `sperre-rueckgabe.gab`,
 * WRITTEN BY HAND IN C (server lane, TODO section 0e, acceptance point 2).
 *
 * HOW THIS FILE WAS WRITTEN, because that is the whole of its value: from the
 * SOURCE of `sperre-rueckgabe.gab`, read as a C programmer would read the
 * English of it -- "take the lock, write 7, read it, release, return what was
 * read" -- and NOT from the emitted C. Nothing here was copied out of
 * `gabbro emit`'s output. If the two agree, that agreement is a statement about
 * the lowering; if they were copies of each other it would be a statement about
 * `cp`.
 *
 * It offers the same two names the driver needs -- `lauf()` as the entry and the
 * unit's lock as `L_nimm`/`L_gib` (provided by the driver, like the emitted C
 * expects them) -- so ONE driver compiles over either side.
 *
 * THE ONE PLACE THIS FILE IS OPINIONATED: `lies_unter_sperre` reads `z` into a
 * local INSIDE the section and returns the local. That is the source's reading
 * of `locks L { z = 7; return z; }` -- the lock is held across the write and the
 * read, so nothing else touches `z` in between. A C programmer who releases
 * first and then evaluates `z` has written a different program: the read is
 * outside the section and the second thread may have run. The instrument holds
 * the emitted C against THIS reading.
 *
 * Threads and stacks: the same runtime as the emitted side
 * (`laufzeit/faden.c`, our own raw `clone`), on this file's own static stacks --
 * a handwritten twin that used libc threading would be measuring two runtimes
 * and not two lowerings.
 */
#include <stdint.h>
#include <stdbool.h>

#define HAND_K 64u

/* The lock: two prototypes and no body, exactly what the emitted C also gets
 * (the driver has the spinlock). */
void L_nimm(void);
void L_gib(void);

/* The thread runtime, named as `laufzeit/faden.h` names it. */
int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort);
void gabbro_faden_warte(uint32_t *wort);

/* `static mut z : u32 = 0;` */
static uint32_t z = 0;

/* `table sicht count 1 { slot { wert : u32 wrapping } }` */
struct hand_sicht_slot {
    uint32_t wert;
};
static struct hand_sicht_slot hand_sicht[1];

/* `table takt count K { slot { an : bool } }` -- all slots false, like the
 * emitted side's zero-initialised storage. */
static bool hand_takt_an[HAND_K];

/* One 64 KiB stack per thread root, 16-aligned as the SysV ABI wants it. */
static unsigned char hand_stapel_leser[65536] __attribute__((aligned(16)));
static unsigned char hand_stapel_nullt[65536] __attribute__((aligned(16)));
static uint32_t hand_wort_leser;
static uint32_t hand_wort_nullt;

/* `impl fn lies_unter_sperre() -> u32 { locks L { z = 7; return z; } }` */
static uint32_t lies_unter_sperre(void)
{
    uint32_t gelesen;
    L_nimm();
    z = 7;
    gelesen = z; /* INSIDE the section -- see the header note. */
    L_gib();
    return gelesen;
}

/* `impl fn leser()` -- K rounds of "read under the lock, add it up under the
 * lock". */
static void leser(void)
{
    for (unsigned i = 0; i < HAND_K; i++) {
        if (hand_takt_an[i] == false) {
            uint32_t v = lies_unter_sperre();
            L_nimm();
            hand_sicht[0].wert = hand_sicht[0].wert + v; /* u32, wrapping */
            L_gib();
        }
    }
}

/* `impl fn nullt()` -- the second thread, writing 0 into the same carrier under
 * the same lock. */
static void nullt(void)
{
    for (unsigned i = 0; i < HAND_K; i++) {
        if (hand_takt_an[i] == false) {
            L_nimm();
            z = 0;
            L_gib();
        }
    }
}

/* `impl fn lauf() -> u32 { start { leser, nullt }; locks L { return … } }` */
static uint32_t lauf(void)
{
    uint32_t antwort;
    if (gabbro_faden_start(leser, hand_stapel_leser + sizeof hand_stapel_leser,
                           &hand_wort_leser) != 0) {
        __builtin_trap();
    }
    if (gabbro_faden_start(nullt, hand_stapel_nullt + sizeof hand_stapel_nullt,
                           &hand_wort_nullt) != 0) {
        __builtin_trap();
    }
    gabbro_faden_warte(&hand_wort_leser);
    gabbro_faden_warte(&hand_wort_nullt);
    L_nimm();
    antwort = hand_sicht[0].wert;
    L_gib();
    return antwort;
}
