/* messung/proben/kmodul/takt.c -- the PROGRAM's bodies for its own kernel
 * calls (server lane, TODO section 0e K3).
 *
 * `sperre-takt.gab` declares three foreign functions and this is what it
 * promised, written by whoever wrote the program -- not by Gabbro. It is the
 * whole of what this probe knows about Linux: an `hrtimer` in HARDIRQ mode,
 * `pr_info`, and `smp_processor_id`. A different kernel gets a different file
 * here and the same `.gab`.
 *
 * WHAT THE TIMER IS FOR. The probe measures that `lock … masks irqs` really
 * masks in a kernel module. For that something has to try to enter while the
 * lock is held, from an interrupt, on the same core -- so this file arms a
 * timer whose body runs in hardirq context and calls the unit's `tick`, which
 * takes the same lock. The thread side holds it across a 4096-slot traversal,
 * which is a window a 50 us timer lands in many times over.
 *
 * THE OBSERVATION, and why the green run is a measurement. Before it takes the
 * lock, the timer body reads `gabbro_halter_TAKT` -- the runtime's record of
 * which core holds `TAKT`, or -1 (`laufzeit/kmodul/sperre.h`). If that ever
 * equals its own core, an interrupt landed INSIDE a critical section on the
 * core that was holding it, which is the same-core deadlock the checker refuses
 * as `H102`. Two counters travel out through `pr_info`:
 *
 *   ticks    how often the timer fired at all. A run with 0 would report a
 *            clean `landed` and have measured NOTHING -- the harness checks it.
 *   landed   how often it fired on a core that was holding. With `masks irqs`
 *            this must be 0; without it the run does not finish, because the
 *            body then waits for the core it interrupted.
 *
 * `hrtimer_forward_now` + `HRTIMER_RESTART` keeps it periodic; `_aus` cancels
 * it before the module's init returns, so nothing of this file outlives the
 * load.
 */

#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/hrtimer.h>
#include <linux/ktime.h>
#include <linux/smp.h>
#include <linux/types.h>
#include <linux/compiler.h>

void gabbro_kmod_takt_melde(uint32_t schluessel, uint64_t wert);
void gabbro_kmod_takt_an(void);
void gabbro_kmod_takt_aus(void);

/* The unit's own body, entered from the interrupt: `pub fn tick` of
 * `sperre-takt.gab`. `pub`, so it is not `static` in the emitted C. */
void tick(void);

/* The runtime's holder record for `TAKT` (`laufzeit/kmodul/sperre.h`). */
extern int gabbro_halter_TAKT;

#define GABBRO_TAKT_NS 50000ull

static struct hrtimer gabbro_takt_uhr;
static u64 gabbro_takt_ticks;
static u64 gabbro_takt_landungen;
static bool gabbro_takt_laeuft;

static enum hrtimer_restart gabbro_takt_schlag(struct hrtimer *u)
{
    gabbro_takt_ticks++;
    if (READ_ONCE(gabbro_halter_TAKT) == smp_processor_id()) {
        gabbro_takt_landungen++;
    }
    tick();
    hrtimer_forward_now(u, ns_to_ktime(GABBRO_TAKT_NS));
    return HRTIMER_RESTART;
}

void gabbro_kmod_takt_melde(uint32_t schluessel, uint64_t wert)
{
    pr_info("gabbro-takt: k=%u v=%llu\n",
            (unsigned int)schluessel, (unsigned long long)wert);
}

void gabbro_kmod_takt_an(void)
{
    gabbro_takt_ticks = 0;
    gabbro_takt_landungen = 0;
    hrtimer_init(&gabbro_takt_uhr, CLOCK_MONOTONIC, HRTIMER_MODE_REL_HARD);
    gabbro_takt_uhr.function = gabbro_takt_schlag;
    gabbro_takt_laeuft = true;
    hrtimer_start(&gabbro_takt_uhr, ns_to_ktime(GABBRO_TAKT_NS),
                  HRTIMER_MODE_REL_HARD);
}

void gabbro_kmod_takt_aus(void)
{
    if (gabbro_takt_laeuft) {
        hrtimer_cancel(&gabbro_takt_uhr);
        gabbro_takt_laeuft = false;
    }
    pr_info("gabbro-takt: ticks=%llu landed=%llu\n",
            (unsigned long long)gabbro_takt_ticks,
            (unsigned long long)gabbro_takt_landungen);
}
