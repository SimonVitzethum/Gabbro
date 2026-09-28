/* messung/proben/kmodul/melde.c -- the PROGRAM's body for its own kernel call.
 *
 * `halde-treiber.gab` declares
 *
 *     extern fn gabbro_kmod_melde(schluessel : u32, wert : u64)
 *         effects { pure } costs <= 64 ops;
 *
 * and this is the body it promised, written by whoever wrote the program --
 * not by Gabbro. It is the whole of what this probe knows about Linux, and it
 * is three lines: `pr_info`. A different kernel gets a different file here and
 * the same `.gab`.
 *
 * The assumption the program named beside the declaration
 * (`kmod_melde_vertrag`, falsifier `sonde_kmod_melde`) is about exactly this
 * body: it writes its two words to the kernel log and returns.
 */

#include <linux/kernel.h>
#include <linux/printk.h>
#include <linux/types.h>

void gabbro_kmod_melde(uint32_t schluessel, uint64_t wert);

void gabbro_kmod_melde(uint32_t schluessel, uint64_t wert)
{
    pr_info("gabbro-halde: k=%u v=%llu\n",
            (unsigned int)schluessel, (unsigned long long)wert);
}
