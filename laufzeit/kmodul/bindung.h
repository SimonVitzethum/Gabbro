/* laufzeit/kmodul/bindung.h -- THE ONLY NAMES THE MODULE RUNTIME CALLS, and
 * every one of them is DEFINED BY THE PROGRAM (server lane, TODO section 0e K7).
 *
 * SIMON'S RULE, 2026-09-27: *"API calls are always user-made."* A Gabbro kernel
 * module reaches the kernel only through items the PROGRAM declares -- with
 * their ABI, their effects, their costs and the assumption their bodies keep.
 * Until 2026-09-28 that held for everything a program wrote and NOT for the
 * runtime beside it: `kmodul.c` called `kthread_run` and `wait_for_completion`,
 * `arena.c` called `vzalloc`, `vfree` and `module_param`, `sperre.h` expanded to
 * `raw_spin_lock_irqsave`, and every one of those twelve names was the runtime's
 * choice (measured, `dokumente/OFFEN.md` O35: the stage `symbole_pruefe` of
 * `instrumente/pruefe-kernelmodul.sh`).
 *
 * THIS FILE IS WHAT REPLACED THEM. Twelve declarations, no definition: the
 * runtime calls these, the program defines them, and the kernel's own names
 * appear in the program's C and nowhere else. `bibliothek/linux-kmod/` is the
 * binding a program may take off the shelf -- ORDINARY USER CODE in the
 * program's own build, listed in its manifest, never a table inside the checker
 * or the runtime. A different kernel gets a different body, not a different
 * Gabbro.
 *
 * WHY THE NAMES STAND HERE AND NOT IN THE PROGRAM. The direction matters. A
 * runtime that read the program's choice of name would need the program's
 * header -- a second register over one fact (`W7`). So the INTERFACE is fixed
 * and the IMPLEMENTATION is the program's, exactly the arrangement the lock
 * primitives already have in the other direction: `emit.rs` declares
 * `L_nimm`/`L_gib` per `lock` and defines neither, and every driver flavour
 * supplies them. What is new since K7 is only that the kernel's side of the
 * runtime is the same kind of hole.
 *
 * AND THE TYPES ARE THE EMITTER'S, TO THE LETTER. A program declares these as
 * ordinary Gabbro `extern fn` items, so the emitted unit C carries their
 * prototypes (`u32` -> `uint32_t`, `u64` -> `uint64_t`, no result -> `void`) --
 * and `kmodul.c` includes BOTH the emitted unit and this header, so a program
 * whose declaration disagrees with the line below is a compile error in the
 * runtime's own translation unit. *That is the check that makes the Gabbro
 * declaration load-bearing rather than decorative:* it is held against this
 * file by the C compiler, on every build.
 *
 * AN ADDRESS TRAVELS AS A `u64`, and that is what makes the whole interface
 * expressible in Gabbro at all. Gabbro has no pointer type -- the same reason a
 * system-call binding passes registers (Opus agent L) -- so a reservation's
 * base, a lock's storage and a root's body all cross as numbers, and the two
 * sides cast. The runtime casts with `(uint64_t)(uintptr_t)`, the program's body
 * casts back; both halves stand beside each other in
 * `bibliothek/linux-kmod/linux-kmod.c`.
 *
 * THE STORAGE IS THE RUNTIME'S, THE OPERATIONS ARE THE PROGRAM'S. A
 * `raw_spinlock_t` and a `struct completion` are kernel TYPES, and their size
 * depends on the kernel's configuration -- so neither can stand in this file.
 * What stands here is a blob of `unsigned long` big enough for either, and the
 * program's body asserts that its own struct fits (`_Static_assert`, in
 * `linux-kmod.c`, against the kernel it is being built for). A blob too small is
 * a loud build error and never a silent overrun.
 *
 * WHAT IS NOT IN HERE, and why it is not a gap:
 *
 *   * `module_init` / `module_exit` / `MODULE_LICENSE` -- declarative macros
 *     that place a pointer or a string in a section. They are the module's
 *     SHAPE, not a call, and they leave no undefined symbol (measured: the stage
 *     `symbole_pruefe` reads 0 with this file in place);
 *   * the memory model of an `atomic` -- `READ_ONCE`, `smp_load_acquire`,
 *     `try_cmpxchg` and friends are macros and inline assembly and would leave
 *     no symbol either, so the measurement above cannot see them. They are bound
 *     the other way: the module target's `<stdatomic.h>` is a REFUSAL in the
 *     runtime (`include/stdatomic.h`) and the program supplies the table
 *     (`bibliothek/linux-kmod/stdatomic.h`, one `.h` line in its manifest). The
 *     build refuses a `module` unit that declares an `atomic` and binds no
 *     memory model, before a byte of C is written (`bau.rs::modulregel`);
 *   * the type shims `stdint.h`, `stdbool.h`, `stddef.h`, `math.h` in
 *     `include/` -- the kernel builds `-nostdinc` and the emitted prelude asks
 *     for them. They map C's names onto the kernel's own types and declare no
 *     function.
 */
#ifndef GABBRO_KMODUL_BINDUNG_H
#define GABBRO_KMODUL_BINDUNG_H

#include <linux/types.h>

/* -- the report channel ---------------------------------------------------- */
/*
 * The runtime has NO WORDS OF ITS OWN inside a kernel module, because printing
 * is a kernel call. So a refusal travels as a CODE and two numbers, and the
 * program's body decides what the kernel log says about it. The codes are
 * closed and listed here; `bibliothek/linux-kmod/linux-kmod.c` carries one
 * sentence per code.
 */
#define GABBRO_KERN_M_DESKRIPTOR   1u /* (max, floor_hi)   bad arena descriptor */
#define GABBRO_KERN_M_ZU_VIELE     2u /* (seen, limit)     more arenas than the runtime maps */
#define GABBRO_KERN_M_BODEN        3u /* (floor_hi, bytes) the provision cannot hold the committed floor */
#define GABBRO_KERN_M_SPANNE       4u /* (max, elem)       the span does not fit size_t */
#define GABBRO_KERN_M_RESERVE      5u /* (bytes, 0)        the reservation itself refused */
#define GABBRO_KERN_M_UEBER_MAX    6u /* (wanted, max)     a `grow` past the declared ceiling: fail-stop */
#define GABBRO_KERN_M_LADEN_ARENA  7u /* (errno, 0)        load refused: a reservation failed */
#define GABBRO_KERN_M_LADEN_ANTWORT 8u /* (answer, 0)      load refused: the unit's init answered non-zero */
#define GABBRO_KERN_M_LADEN_STOPP  9u /* (errno, 0)        load refused: a fail-stop fired during init */
#define GABBRO_KERN_M_LADEN_FADEN 10u /* (errno, 0)        load refused: a declared root did not start */

void gabbro_kern_melden(uint32_t code, uint64_t a, uint64_t b);

/* -- the arena's storage --------------------------------------------------- */
/*
 * `reserve` answers the base address of `bytes` zeroed bytes, or 0 -- which is
 * the whole of what the bounded heap needs from the kernel (`arena.c` decides
 * the rest, and `Spec.lean` (M10) says why the module flavour's ceiling is a
 * budget). `vorrat` is the module's PROVISION in bytes: a number the deployment
 * sets, which is why it is a call and not a constant -- in
 * `bibliothek/linux-kmod` it is a `module_param`, and `param_ops_uint` was one
 * of the twelve names that moved out of the runtime with it.
 */
uint64_t gabbro_kern_reserve(uint64_t bytes);
void gabbro_kern_freigeben(uint64_t basis);
uint64_t gabbro_kern_vorrat(void);

/* -- the locks ------------------------------------------------------------- */
/*
 * One blob per `lock`, owned by the runtime (`sperre.h`), initialised once at
 * load, and passed as a number to every operation. The MASKED pair is a
 * separate pair of names and not a flag, because `masks irqs` is a promise
 * about the environment and the program has to be able to keep it with a
 * different primitive (`raw_spin_lock_irqsave` in `bibliothek/linux-kmod`) --
 * and because the flags word belongs to the program's struct, inside the blob,
 * where the release finds it again.
 *
 * `kernnummer` is the core that is running, for the HOLDER observation in
 * `sperre.h` -- the thing that makes a green `takt` run a measurement instead
 * of an absence of bad news.
 */
#define GABBRO_KERN_SPERRE_WORTE 32
#define GABBRO_KERN_FADEN_WORTE 32

void gabbro_kern_sperre_init(uint64_t s);
void gabbro_kern_sperre_nimm(uint64_t s);
void gabbro_kern_sperre_gib(uint64_t s);
void gabbro_kern_sperre_nimm_maskiert(uint64_t s);
void gabbro_kern_sperre_gib_maskiert(uint64_t s);
uint32_t gabbro_kern_kernnummer(void);

/* -- the roots as kernel threads ------------------------------------------ */
/*
 * `start` takes the blob and the ADDRESS OF THE ROOT'S WRAPPER (`int f(void *)`
 * in the runtime, cast to a number) and answers 0 or an error. The program's
 * body owns the whole thread lifecycle -- it creates the thread, it runs the
 * wrapper, it signals when the wrapper returned -- so the runtime needs no
 * "I am done" call and a failed start is completed by the body itself, which
 * is what keeps `warte` from hanging on a thread that never ran.
 */
uint32_t gabbro_kern_faden_start(uint64_t f, uint64_t koerper);
void gabbro_kern_faden_warte(uint64_t f);

#endif
