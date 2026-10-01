/* bibliothek/linux-kmod/linux-kmod.c -- the handwritten C left in a Gabbro kernel
 * module: the core number and the thread pair `gabbro_kern_faden_start`/`_warte` that
 * `linux-kmod.gab` declares (server lane K7, 2026-09-28; cut to this by the C-free
 * lane's C2 slice 2, 2026-09-30).
 *
 * Everything else the binding does is Gabbro in `linux-kmod.gab` since C2: the
 * report channel over the kernel's variadic `_printk`, the load verdict, the lock
 * operations over `_raw_spin_*`, the core number (one `%gs` load). What stays here
 * is a WALL, written down rather than hidden:
 *
 *   * the kernel's thread start takes a FUNCTION POINTER to run on the new thread
 *     (`kthread_create_on_node(threadfn, data, …)`). A Gabbro `extern fn` that took
 *     one could start a thread the checker's concurrency rules never see -- the
 *     hosted twin of that hole is `N572`, closed by the checked `child` region and
 *     the proved trampoline `tor.trampolin`. The kernel needs its own checked form;
 *     until it exists, the start is this C, called by the generated driver only;
 *   * its answer is a pointer OR an errno in one word (`ERR_PTR`), a decoding
 *     Gabbro has for gate answers (`tor.region`) and not for an `extern fn`;
 *   * the join is a `struct completion`, a kernel type of configuration-dependent
 *     layout, kept in the driver's 32-word blob (`_Static_assert` below);
 *   * the core number is a read of the kernel's per-CPU DATA symbol `pcpu_hot`,
 *     and Gabbro has no declaration of a foreign data object.
 *
 * `zaehle-c.py` counts this file (kmod target); its removal is C2's next step.
 */

#include <linux/smp.h>
#include <linux/kthread.h>
#include <linux/completion.h>
#include <linux/err.h>
#include <linux/string.h>

/* The thread blob the generated module driver hands over (`treiber.rs`,
 * `erzeuge_kmod`: 32 words per root). The driver carries the prototypes of both
 * functions below, so the C compiler holds each definition against them. */
#define GABBRO_KERN_FADEN_WORTE 32

uint32_t gabbro_kern_kernnummer(void);
uint32_t gabbro_kern_faden_start(uint64_t f, uint64_t koerper);
void gabbro_kern_faden_warte(uint64_t f);

/* -- the core number ------------------------------------------------------- */
uint32_t gabbro_kern_kernnummer(void)
{
    return (uint32_t)raw_smp_processor_id();
}

/* -- the roots as kernel threads ------------------------------------------- */
/*
 * `struct completion` AND NOT `kthread_stop`. A Gabbro root is a function that
 * returns when it is done; it never asks whether it should stop, so
 * `kthread_stop` -- which sets a flag and waits for the thread to notice --
 * would be the wrong instrument, and on a thread that has already returned it
 * needs a reference nobody holds. A completion is exactly the thing: the thread
 * signals once, at the end, and the waiter is woken.
 *
 * A start that FAILS completes at once, which is what the runtime relies on:
 * its load refusal waits for every root it tried to start, and a blob that
 * never completed would hang `insmod` instead of refusing it
 * (the generated module driver, `treiber.rs::erzeuge_kmod`).
 */
struct gabbro_kern_faden {
    struct completion fertig;
    int (*koerper)(void *);
    struct task_struct *aufgabe;
};

_Static_assert(sizeof(struct gabbro_kern_faden)
                   <= GABBRO_KERN_FADEN_WORTE * sizeof(unsigned long),
               "this kernel's struct completion does not fit the runtime's thread blob "
               "-- raise the thread blob in the generated driver (treiber.rs)");
_Static_assert(__alignof__(struct gabbro_kern_faden) <= __alignof__(unsigned long),
               "this kernel's struct completion wants more alignment than the runtime's "
               "thread blob has");

static struct gabbro_kern_faden *faden(uint64_t f)
{
    return (struct gabbro_kern_faden *)(uintptr_t)f;
}

static int gabbro_kern_faden_lauf(void *p)
{
    struct gabbro_kern_faden *f = p;

    f->koerper(NULL);
    complete(&f->fertig);
    return 0;
}

uint32_t gabbro_kern_faden_start(uint64_t f, uint64_t koerper)
{
    static unsigned int nummer;
    struct task_struct *t;

    memset(faden(f), 0, sizeof(struct gabbro_kern_faden));
    init_completion(&faden(f)->fertig);
    faden(f)->koerper = (int (*)(void *))(uintptr_t)koerper;
    t = kthread_run(gabbro_kern_faden_lauf, faden(f), "gabbro/%u", nummer++);
    if (IS_ERR(t)) {
        /* Nobody will signal, so the binding does it here -- see the note
         * above: the runtime waits for this blob either way. */
        complete(&faden(f)->fertig);
        return (uint32_t)(-PTR_ERR(t));
    }
    faden(f)->aufgabe = t;
    return 0;
}

void gabbro_kern_faden_warte(uint64_t f)
{
    wait_for_completion(&faden(f)->fertig);
}
