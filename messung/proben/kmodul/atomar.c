/* messung/proben/kmodul/atomar.c -- the PROGRAM's bodies for its own kernel
 * calls (server lane, TODO section 0e K6).
 *
 * `atomar-faeden.gab` declares two foreign functions and this is what it
 * promised, written by whoever wrote the program -- not by Gabbro. It is the
 * whole of what this probe knows about Linux: `pr_info` and `panic`. A
 * different kernel gets a different file here and the same `.gab`.
 *
 * **There are no threads in this file, and that is the point of the probe.**
 * Its twin next door (`takt.c`) arms a kernel timer, because an interrupt is
 * something the checker cannot see and the program's own C has to bring. The
 * two threads here are DECLARED -- `concurrent { erzeuger, verbraucher }` --
 * so `gabbro build` writes them into `wurzeln.h` and
 * `laufzeit/kmodul/kmodul.c` starts one `kthread` per root and joins them
 * before the unload function runs. Nothing about kthreads belongs to the
 * program.
 *
 * `aufgegeben` IS THE BOUNDED CAS LOOP'S EXIT, and a fail-stop is the only
 * honest body for it. The declaration says `-> never effects { diverges }`, so
 * the emitted C is `_Noreturn void aufgegeben(void)` and a body that returned
 * would be a lie the compiler cannot catch on the caller's side. It is never
 * called in a green run: two threads over 256 rounds do not lose eight races in
 * a row on one increment.
 */

#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/types.h>

void gabbro_kmod_atomar_melde(uint32_t schluessel, uint64_t wert);
_Noreturn void aufgegeben(void);

void gabbro_kmod_atomar_melde(uint32_t schluessel, uint64_t wert)
{
    pr_info("gabbro-atomar: k=%u v=%llu\n",
            (unsigned int)schluessel, (unsigned long long)wert);
}

_Noreturn void aufgegeben(void)
{
    panic("gabbro-atomar: a bounded CAS loop exceeded its declared passes\n");
}
