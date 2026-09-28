/* laufzeit/bindung.h -- THE NAMES THE HOSTED RUNTIME CALLS, and every one of
 * them is DEFINED BY THE PROGRAM (server lane, TODO section 0e K8).
 *
 * SIMON'S RULE, drawn for the runtimes on 2026-09-28: *"an die Hardware ist OK,
 * OS nicht, das muss selbst gemacht werden"* -- no operating-system call is
 * hard-wired in any runtime; hardware access on bare metal stays allowed,
 * because an instruction is not an API. K7 did this for the module runtime and
 * `laufzeit/kmodul/bindung.h` is its interface; THIS FILE IS THE HOSTED TWIN,
 * built to the same three rules and deliberately in the same order, so that the
 * two can be read against each other:
 *
 *   * the INTERFACE is fixed and the IMPLEMENTATION is the program's (a runtime
 *     that read the program's choice of name would need the program's header --
 *     a second register over one fact, `W7`);
 *   * an ADDRESS TRAVELS AS A `u64`, because Gabbro has no pointer type -- the
 *     same reason a system-call binding passes registers (Opus agent L). Both
 *     sides cast, and both casts stand beside each other in
 *     `bibliothek/linux/linux.c`;
 *   * the STORAGE is the runtime's, the OPERATIONS are the program's.
 *
 * WHAT IS BOUND HERE TODAY, AND WHAT IS NOT -- and the difference is measured,
 * not asserted. `instrumente/pruefe-os-bindung.sh` reads what the hosted runtime
 * still pulls out of the operating system (`nm -u` over a built binary,
 * intersected with the runtime's own objects), and its mark is the worklist:
 *
 *   bound since this file exists   `mmap`, `mprotect`, `sysconf`, and the
 *                                  `fprintf`/`exit`/`abort` of the bounded
 *                                  heap's fail-stops -- all of `arena_dyn.c`
 *   still the runtime's            the generated driver's `pthread_*` and
 *                                  `pause`, `start.c`/`start_pool.c`, and the
 *                                  raw `clone`/`futex` of `faden.c` (which
 *                                  leave no symbol at all -- the instrument's
 *                                  second stage counts those sites instead)
 *
 * *The mark goes down when a line moves out of the runtime, and the instrument
 * refuses a run that needs MORE -- so this file cannot grow a hidden OS call
 * back.*
 *
 * WHY THE HOSTED ARENA NEEDS EXACTLY THREE CALLS AND THE MODULE ONE NEEDS
 * THREE OTHERS. The arithmetic is the same in both (`arena_dyn.h`: the ceiling
 * is a number, the committed prefix is storage, refuse-on-full is the
 * runtime's), and what differs is the primitive underneath: hosted Linux can
 * name address space WITHOUT storage, so a reservation is `mmap(PROT_NONE)` and
 * a commit is `mprotect` over a page-aligned tail; a loadable module has no
 * exported primitive for that and its ceiling is a budget
 * (`laufzeit/kmodul/arena.c`). The page rounding stays on the runtime's side --
 * the binding answers the page SIZE and never decides where a page begins.
 *
 * THE REPORT CHANNEL IS A CODE AND TWO NUMBERS, for the same reason the module
 * one is: printing is an OS call, so the runtime has no words of its own. What
 * the reader sees is the program's sentence; `bibliothek/linux/linux.c` carries
 * one per code, on standard error, in the same shape the runtime printed before
 * this file existed.
 *
 * `gabbro_os_ende` DOES NOT RETURN -- and every call site is written as if it
 * might. It cannot be declared `_Noreturn`: the program declares it as an
 * ordinary Gabbro `extern fn`, the emitted prototype is `void f(uint32_t)`, and
 * the two declarations meet in one translation unit. So the runtime's own code
 * carries a fail-closed line behind every call (`return false`, or a return from
 * the reservation with `base` still null), and a binding whose body returned
 * would leave the caller in the `else` it wrote rather than in a program that
 * silently continued past a fail-stop. *The weaker declaration costs one line
 * per site and buys the check that the Gabbro declaration is load-bearing.*
 */
#ifndef GABBRO_BINDUNG_H
#define GABBRO_BINDUNG_H

#include <stdint.h>

/* -- the report channel and the stop ---------------------------------------
 *
 * The codes are closed and listed here; the two numbers beside each one are
 * what the program's sentence may name. `gabbro_os_ende` takes the process
 * status a fail-stop ends with -- `GABBRO_ARENA_EXIT_RESERVE` for a refused
 * reservation, `GABBRO_OS_ENDE_ABBRUCH` where the runtime used to call
 * `abort()`.
 */
#define GABBRO_OS_M_DESKRIPTOR 1u /* (max, floor_hi)  a descriptor the emitter misbuilt */
#define GABBRO_OS_M_SPANNE     2u /* (max, elem)      the span does not fit `size_t` */
#define GABBRO_OS_M_RESERVE    3u /* (max, bytes)     the reservation itself refused */
#define GABBRO_OS_M_BODEN      4u /* (floor_hi, 0)    the committed floor would not commit */
#define GABBRO_OS_M_UEBER_MAX  5u /* (wanted, max)    a `grow` past the declared ceiling */
#define GABBRO_OS_M_SEITE      6u /* (0, 0)           the page size is not answerable */

/* The status a fail-stop leaves behind. The reservation's is the one
 * `arena_dyn.h` already names and the corpus already reads; the second is for
 * the places the runtime called `abort()`, which had none. */
#define GABBRO_OS_ENDE_ABBRUCH 134u /* what a shell reports for SIGABRT: 128 + 6 */

void gabbro_os_melden(uint32_t code, uint64_t a, uint64_t b);
void gabbro_os_ende(uint32_t code);

/* -- the bounded heap's storage --------------------------------------------
 *
 * `reserve` answers the base of `bytes` of RESERVED-BUT-NOT-COMMITTED address
 * space, or 0; `commit` makes `[versatz, versatz + bytes)` of it readable and
 * writable and answers 0 on success; `seitengroesse` is the granularity the
 * runtime rounds its commits to. Nothing here scrubs: the reservation reads as
 * zero until written, which is a property of the mapping the binding chose and
 * is named in `bibliothek/linux/linux.gab` as such.
 */
uint64_t gabbro_os_reserve(uint64_t bytes);
uint32_t gabbro_os_commit(uint64_t basis, uint64_t versatz, uint64_t bytes);
uint64_t gabbro_os_seitengroesse(void);

#endif
