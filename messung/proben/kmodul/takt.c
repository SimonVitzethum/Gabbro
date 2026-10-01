/* messung/proben/kmodul/takt.c -- the PROGRAM's bodies for its own kernel
 * calls (server lane, TODO section 0e K3).
 *
 * `sperre-takt.gab` declares three foreign functions and this is what it
 * promised, written by whoever wrote the program -- not by Gabbro. It is the
 * whole of what this probe knows about Linux: an `hrtimer` in HARDIRQ mode and
 * `pr_info`. A different kernel gets a different file here and the same `.gab`.
 *
 * WHY IT IS STILL C (C-free lane, C2 slice 3, 2026-10-01). It is the probe's
 * HARNESS, not product: on this kernel (6.8) an hrtimer's callback is a FIELD of
 * `struct hrtimer` (`hrtimer_init` + `timer.function = …`), a kernel layout and a
 * code address stored into memory -- neither is a form Gabbro has (code reaches a
 * foreign body only as an `entry fn` ARGUMENT, `N575`-`N577`). Kernels from 6.13
 * take the callback as an argument (`hrtimer_setup`). Counted by `zaehle-c.py`.
 *
 * WHAT THE TIMER IS FOR. The probe measures that `lock … masks irqs` really
 * masks in a kernel module. For that something has to try to enter while the
 * lock is held, from an interrupt, on the same core -- so this file arms a
 * timer whose body runs in hardirq context and calls the unit's `tick`, which
 * takes the same lock. The thread side holds it across a 4096-slot traversal,
 * which is a window a 50 us timer lands in many times over.
 *
 * THE OBSERVATION, and why the green run is a measurement. The probe runs on
 * ONE core: the timer is armed there and the critical sections run there. An
 * interrupt that landed INSIDE one would take `TAKT` while the core it
 * interrupted holds it -- the same-core deadlock the checker refuses as `H102`
 * -- and the run would never finish (the harness's gift 5 is exactly that).
 * So a run that finishes says no tick landed inside, and `ticks` says how
 * often the timer had the chance: a run with 0 ticks finishes too and has
 * measured NOTHING -- the harness demands a minimum.
 *
 * (Until 2026-10-01 the timer body also compared the runtime's holder record
 * `gabbro_halter_TAKT` with its own core and counted `landed`. On one core
 * that count could only ever be 0 in a run that finished; the record and the
 * core number behind it were the module runtime's last C, and went with it.)
 *
 * `hrtimer_forward_now` + `HRTIMER_RESTART` keeps it periodic; `_aus` cancels
 * it before the module's init returns, so nothing of this file outlives the
 * load.
 */

#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/hrtimer.h>
#include <linux/ktime.h>
#include <linux/types.h>
#include <linux/compiler.h>

void gabbro_kmod_takt_melde(uint32_t schluessel, uint64_t wert);
void gabbro_kmod_takt_an(void);
void gabbro_kmod_takt_aus(void);

/* The unit's own body, entered from the interrupt: `pub fn tick` of
 * `sperre-takt.gab`. `pub`, so it is not `static` in the emitted C. */
void tick(void);


#define GABBRO_TAKT_NS 50000ull

static struct hrtimer gabbro_takt_uhr;
static u64 gabbro_takt_ticks;
static bool gabbro_takt_laeuft;

static enum hrtimer_restart gabbro_takt_schlag(struct hrtimer *u)
{
    gabbro_takt_ticks++;
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
    pr_info("gabbro-takt: ticks=%llu\n", (unsigned long long)gabbro_takt_ticks);
}
