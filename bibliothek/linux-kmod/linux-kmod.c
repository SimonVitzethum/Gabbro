/* bibliothek/linux-kmod/linux-kmod.c -- THE BODIES of the twelve primitives
 * `linux-kmod.gab` declares (server lane, TODO section 0e K7, 2026-09-28).
 *
 * **THIS FILE IS THE ONE PLACE A LINUX KERNEL FUNCTION IS NAMED**, and it is a
 * file of the PROGRAM: a manifest lists it, the module's own build compiles it,
 * and whoever wants a different kernel writes a different one. The Gabbro tree
 * around it names none of these functions -- not the checker, not the emitter,
 * not the module runtime (`laufzeit/kmodul/bindung.h` declares what the runtime
 * calls and defines nothing). That is Simon's binding constraint, 2026-09-27:
 * *"API calls are always user-made."*
 *
 * What stood here before K7 -- measured, not remembered
 * (`dokumente/OFFEN.md` O35): `vzalloc`, `vfree`, `param_ops_uint` (from
 * `module_param`) and `_printk` came out of `laufzeit/kmodul/arena.c`;
 * `_raw_spin_lock_irqsave`, `_raw_spin_unlock_irqrestore` and `pcpu_hot` (from
 * `smp_processor_id`) out of `sperre.h`; `kthread_create_on_node`,
 * `wake_up_process`, `complete`, `wait_for_completion` and
 * `__init_swait_queue_head` out of `kmodul.c`. Twelve names, and they are all
 * below now.
 *
 * WHY THE KERNEL'S TYPES LIVE ON THIS SIDE. A `raw_spinlock_t` and a
 * `struct completion` are as much the kernel's as `raw_spin_lock` is, and their
 * SIZE depends on its configuration. So the runtime hands over a blob of words
 * and this file lays its own structs into it -- with a `_Static_assert` that
 * they fit, held against the very kernel the module is being built for. *A blob
 * too small is a loud build error and never a silent overrun.*
 *
 * WHAT MAKES THE MASKED PAIR THE MASKED PAIR. `raw_spin_lock_irqsave`, and the
 * assumption `kern_bindung_maskiert` of the declaration file is exactly the
 * promise it keeps. `raw_spinlock_t` and not `spinlock_t`: on a `PREEMPT_RT`
 * kernel a `spinlock_t` is a sleeping lock, so a holder can be descheduled and a
 * Gabbro lock's declared holding time (`held <= N ops`) would mean nothing.
 * Stronger than asked, never weaker.
 */

#include <linux/module.h>
#include <linux/moduleparam.h>
#include <linux/vmalloc.h>
#include <linux/printk.h>
#include <linux/spinlock.h>
#include <linux/smp.h>
#include <linux/kthread.h>
#include <linux/completion.h>
#include <linux/err.h>
#include <linux/string.h>

/* The interface, so that every definition below is held against the
 * declaration the runtime calls -- and, through the emitted unit's prototypes,
 * against what the program declared in Gabbro. */
#include "bindung.h"

/* -- the report channel ---------------------------------------------------- */
/*
 * One sentence per code. The runtime hands over a number because printing is a
 * kernel call; the WORDS are the program's, and this is where they stand. A code
 * this binding does not know is still reported -- a silent drop would make a
 * refusal look like a successful load.
 */
void gabbro_kern_melden(uint32_t code, uint64_t a, uint64_t b)
{
    switch (code) {
    case GABBRO_KERN_M_DESKRIPTOR:
        pr_err("gabbro: arena reserve refused: bad descriptor (max=%llu, floor=%llu)\n",
               a, b);
        break;
    case GABBRO_KERN_M_ZU_VIELE:
        pr_err("gabbro: arena reserve refused: more arenas (%llu) than this runtime maps (%llu)\n",
               a, b);
        break;
    case GABBRO_KERN_M_BODEN:
        pr_err("gabbro: arena reserve refused: the provision (%llu bytes) cannot hold the committed floor (%llu slots)\n",
               b, a);
        break;
    case GABBRO_KERN_M_SPANNE:
        pr_err("gabbro: arena reserve refused: the span does not fit size_t (max=%llu, elem=%llu)\n",
               a, b);
        break;
    case GABBRO_KERN_M_RESERVE:
        pr_err("gabbro: arena reserve refused: vzalloc of %llu byte(s) failed\n", a);
        break;
    case GABBRO_KERN_M_UEBER_MAX:
        pr_err("gabbro: arena grow past max (%llu > %llu) -- fail-stop\n", a, b);
        break;
    case GABBRO_KERN_M_LADEN_ARENA:
        pr_err("gabbro: load refused -- a reservation failed (%llu)\n", a);
        break;
    case GABBRO_KERN_M_LADEN_ANTWORT:
        pr_err("gabbro: load refused -- the unit answered %llu\n", a);
        break;
    case GABBRO_KERN_M_LADEN_STOPP:
        pr_err("gabbro: load refused -- a fail-stop fired during init (%llu)\n", a);
        break;
    case GABBRO_KERN_M_LADEN_FADEN:
        pr_err("gabbro: load refused -- a declared root did not start (%llu)\n", a);
        break;
    default:
        pr_err("gabbro: runtime report %u (%llu, %llu) -- this binding has no sentence for it\n",
               code, a, b);
        break;
    }
}

/* -- the arena's storage --------------------------------------------------- */
/*
 * `vzalloc` and not `vmalloc`: the runtime's contract with the program is that a
 * reservation is ZEROED (`laufzeit/arena_dyn.h`).
 *
 * The provision is a module parameter -- `insmod <module>.ko vorrat_kib=24` --
 * and the default is small ON PURPOSE, so that a program's refuse-on-full path
 * is exercised rather than assumed. *The ceiling stays the program's `max`; this
 * is only the storage behind it.*
 */
static unsigned int vorrat_kib = 16;
module_param(vorrat_kib, uint, 0444);
MODULE_PARM_DESC(vorrat_kib,
    "per-arena commit provision in KiB (the ceiling is the program's `max`)");

uint64_t gabbro_kern_reserve(uint64_t bytes)
{
    void *p;

    if (bytes == 0 || bytes > (uint64_t)(~(size_t)0)) {
        return 0;
    }
    p = vzalloc((size_t)bytes);
    return (uint64_t)(uintptr_t)p;
}

void gabbro_kern_freigeben(uint64_t basis)
{
    vfree((void *)(uintptr_t)basis);
}

uint64_t gabbro_kern_vorrat(void)
{
    return (uint64_t)vorrat_kib * 1024ull;
}

/* -- the locks ------------------------------------------------------------- */
/*
 * THE FLAGS WORD IS IN THIS STRUCT, and that is sound for the same reason it is
 * on bare metal: it is written only by the thread that holds the lock, between
 * the acquire and the release, and read only by that same thread. The interface
 * carries no flags argument, because the emitter's `L_nimm`/`L_gib` take none
 * and nothing may travel on their stack.
 */
struct gabbro_kern_sperre {
    raw_spinlock_t s;
    unsigned long flaggen;
};

_Static_assert(sizeof(struct gabbro_kern_sperre)
                   <= GABBRO_KERN_SPERRE_WORTE * sizeof(unsigned long),
               "this kernel's raw_spinlock_t does not fit the runtime's lock blob "
               "-- raise GABBRO_KERN_SPERRE_WORTE in laufzeit/kmodul/bindung.h");
_Static_assert(__alignof__(struct gabbro_kern_sperre) <= __alignof__(unsigned long),
               "this kernel's raw_spinlock_t wants more alignment than the runtime's "
               "lock blob has");

static struct gabbro_kern_sperre *sperre(uint64_t s)
{
    return (struct gabbro_kern_sperre *)(uintptr_t)s;
}

void gabbro_kern_sperre_init(uint64_t s)
{
    memset(sperre(s), 0, sizeof(struct gabbro_kern_sperre));
    raw_spin_lock_init(&sperre(s)->s);
}

void gabbro_kern_sperre_nimm(uint64_t s)
{
    raw_spin_lock(&sperre(s)->s);
}

void gabbro_kern_sperre_gib(uint64_t s)
{
    raw_spin_unlock(&sperre(s)->s);
}

void gabbro_kern_sperre_nimm_maskiert(uint64_t s)
{
    unsigned long f;

    raw_spin_lock_irqsave(&sperre(s)->s, f);
    sperre(s)->flaggen = f;
}

void gabbro_kern_sperre_gib_maskiert(uint64_t s)
{
    unsigned long f = sperre(s)->flaggen;

    raw_spin_unlock_irqrestore(&sperre(s)->s, f);
}

uint32_t gabbro_kern_kernnummer(void)
{
    return (uint32_t)smp_processor_id();
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
 * (`laufzeit/kmodul/bindung.h`).
 */
struct gabbro_kern_faden {
    struct completion fertig;
    int (*koerper)(void *);
    struct task_struct *aufgabe;
};

_Static_assert(sizeof(struct gabbro_kern_faden)
                   <= GABBRO_KERN_FADEN_WORTE * sizeof(unsigned long),
               "this kernel's struct completion does not fit the runtime's thread blob "
               "-- raise GABBRO_KERN_FADEN_WORTE in laufzeit/kmodul/bindung.h");
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
