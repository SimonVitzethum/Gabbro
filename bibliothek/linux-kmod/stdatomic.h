/* bibliothek/linux-kmod/stdatomic.h -- a Gabbro `atomic` LOWERED ONTO THE
 * LINUX KERNEL'S OWN MEMORY MODEL (server lane, TODO section 0e K6, 2026-09-28;
 * moved out of the runtime into this library by K7 the same day).
 *
 * **THIS FILE IS USER CODE.** It is part of the LIBRARY a program takes off the
 * shelf to talk to a Linux kernel, not part of Gabbro's runtime: a program names
 * it in its manifest (one `.h` line beside the `.gab` and `.c` of
 * `bibliothek/linux-kmod`), the build copies it into the module's include
 * directory in place of the runtime's refusing stub
 * (`laufzeit/kmodul/include/stdatomic.h`), and `gabbro build` refuses a `module`
 * unit that declares an `atomic` and names no such file at all. *A different
 * kernel gets a different table and not a different Gabbro* -- which is Simon's
 * binding constraint applied to the memory model (`AUFTRAG-1.md` K7,
 * 2026-09-28: the atomic primitives belong in the program too).
 *
 * Before K6 there was no table anywhere: `_Atomic` was `#define`d to an unknown
 * identifier, so a unit that declared an `atomic` did not become a kernel
 * module at all (and since session 3 `gabbro build` said so one door earlier,
 * `bau.rs::modulregel`). The reason was never that the lowering is hard; it was
 * that a lowering nobody had related to the goal theorem's atomic rely would
 * make the wall green and the claim false. Simon tasked the lowering on
 * 2026-09-28 (`AUFTRAG-1.md` K6) together with the shape of the argument: the
 * relation is a NAMED ASSUMPTION beside the other C-side ones in
 * `grammatik/Grammatik/Zielsatz/Spec.lean`, not a Lean proof of LKMM
 * refinement. That assumption is (M11); its review is
 * `messung/SERVER-0E-SPEC-DIFF.md` section 6. **Read it before changing a line
 * here: every macro below is one row of it.** *(M11) is about the ROWS and not
 * about the file they stand in, so moving them changed nothing in it.*
 *
 * WHY THE MAPPING LIVES IN A HEADER AND NOT IN THE EMITTER. Two reasons, and
 * the first is a hard constraint of this tree:
 *
 *   1. The emitted C is PINNED BYTE FOR BYTE in the translation-validation
 *      chain (`grammatik/Grammatik/CText104.lean`, `a2_104 := rfl`). An emitter
 *      that wrote `smp_load_acquire` for one target and
 *      `atomic_load_explicit` for another would fork the artefact the chain
 *      reads, and the chain would have to be re-proved per target.
 *   2. The surface is CLOSED and small: the emitter can write nine call forms
 *      and one qualifier, no more (`emit.rs`: the two access arms, the five
 *      `holform` rows, the two compare-exchange arms). A closed surface is
 *      exactly what a header can cover completely -- and a form or an ordering
 *      that is NOT in the table below pastes to an undefined name, which the
 *      kernel build refuses. *Silence is not among the answers.*
 *
 * The other half of Simon's rule -- "every API call is the program's" -- is
 * kept by WHERE THIS FILE STANDS and not by an argument about what a macro is.
 * *Session 5 made that argument and it was half right:* nothing below is a
 * kernel FUNCTION, `READ_ONCE` and `try_cmpxchg` leave no symbol, and the
 * link-level measurement of K7 (`symbole_pruefe`) therefore cannot see them at
 * all. But "no undefined symbol" is not "the program chose it" -- the lock
 * primitives it compared itself to (`raw_spin_lock_irqsave`, then in
 * `laufzeit/kmodul/sperre.h`) were on K7's worklist that very day. So the table
 * moved into the library instead, and the rule holds in one reading for both:
 * **a name the kernel gives meaning to stands in the program's own files.**
 *
 * THE MAPPING, one row per ordering, and each row at least as strong as the
 * C11 operation it replaces. What each row RELIES ON is named, because a
 * weak-memory port has to be able to check it -- this table is deliberately
 * argued from the kernel's portable API and NOT from x86-TSO (aarch64 and
 * RISC-V come later; `CLAUDE.md` keeps aarch64 sealed until then):
 *
 *   | C11                         | kernel                       | relies on |
 *   |-----------------------------|------------------------------|-----------|
 *   | load relaxed                | `READ_ONCE`                  | single-copy atomicity for an aligned scalar of 1/2/4/8 bytes; no ordering claimed either side |
 *   | load acquire                | `smp_load_acquire`           | the kernel's acquire load orders this read before every later access, on every architecture |
 *   | load seq_cst                | `smp_mb` + acquire + `smp_mb`| the leading/trailing full-fence mapping of an SC load |
 *   | store relaxed               | `WRITE_ONCE`                 | as above, write side |
 *   | store release               | `smp_store_release`          | the kernel's release store orders every earlier access before this write |
 *   | store seq_cst               | `smp_mb` + `smp_store_mb`    | the leading/trailing full-fence mapping of an SC store |
 *   | fetch_* relaxed             | `try_cmpxchg_relaxed` loop   | a successful cmpxchg is one read-modify-write on the location |
 *   | fetch_* acq_rel             | `try_cmpxchg` loop           | the unsuffixed form is FULLY ordered -- stronger than acq_rel, never weaker |
 *   | fetch_* seq_cst             | `smp_mb` + `try_cmpxchg` + `smp_mb` | as above, with the SC fences |
 *   | cmpxchg (relaxed, relaxed)  | `try_cmpxchg_relaxed`        | same shape and same answer as C11's: bool, and the observed value into `*expected` |
 *   | cmpxchg (release, acquire)  | `try_cmpxchg_release`, `smp_mb` on FAILURE | see the note on failure below |
 *   | cmpxchg (seq_cst, seq_cst)  | `smp_mb` + `try_cmpxchg` + `smp_mb` | the fences carry both the success and the failure path |
 *
 * THE FAILURE PATH OF A COMPARE-EXCHANGE IS THE ONE TRAP HERE, and it is the
 * place where the obvious mapping would be WEAKER than what it replaces.
 * C11 gives a compare-exchange two orderings, and the emitter writes
 * `(memory_order_release, memory_order_acquire)` for an ordered atomic: on a
 * failed exchange the load still has to be an ACQUIRE. In the Linux model a
 * failed cmpxchg implies NO ordering at all -- not even for the unsuffixed,
 * "fully ordered" form (`Documentation/atomic_t.txt`). So the failure path
 * carries its own `smp_mb()` here. Dropping it would be the exact shape of a
 * guarantee traded for a simpler mapping.
 *
 * WHAT IS STILL REFUSED, and by whom:
 *
 *   * a floating-point `atomic` -- `_Generic` below, and `bau.rs::modulregel`
 *     one door earlier. Kernel code may not touch the FPU without
 *     `kernel_fpu_begin`/`_end`, which nothing here declares, and a lowering
 *     that quietly used SSE registers would corrupt whatever userspace task
 *     happened to be scheduled. No barrier repairs that;
 *   * a read-modify-write on an atomic whose width the target's native
 *     `try_cmpxchg` does not cover (`GABBRO_KMOD_ATOMAR_BREITE`). 4 bytes and
 *     the machine word are covered everywhere the kernel runs; a 64-bit RMW on
 *     a 32-bit port needs `try_cmpxchg64`, which this table does not select,
 *     and a 1- or 2-byte RMW is not available on every architecture. LOADS and
 *     STORES are unaffected -- `READ_ONCE`/`WRITE_ONCE`/`smp_*` cover 1, 2, 4
 *     and 8 bytes on every architecture -- so a `bool` flag is fine and only
 *     an `exchange` on one is refused;
 *   * an ordering or a call form that is not in the table: it pastes to an
 *     undefined name and the kernel build stops.
 *
 * `_Atomic` BECOMES `volatile`, and that is not the atomicity -- it is the
 * damage limit. Every access the emitter writes goes through the macros below,
 * which is measured over the whole corpus by
 * `instrumente/pruefe-atomar-zugriffe.py` (token level, not line level). If a
 * site ever escaped that check, `volatile` would still keep the compiler from
 * tearing, fusing or inventing the access -- the silent failures -- while
 * leaving it unordered. It buys strictly less than `_Atomic` and strictly more
 * than nothing, and it is not a reason to skip the check.
 */
#ifndef GABBRO_KMOD_STDATOMIC_H
#define GABBRO_KMOD_STDATOMIC_H

#include <linux/compiler.h>
#include <linux/atomic.h>
#include <linux/types.h>

#define _Atomic volatile

/* -- what every access asserts about the object ---------------------------- */

/* The controlling expression of a `_Generic` is NOT evaluated and loses its
 * qualifiers, so this costs no load and works through the `volatile` above.
 * (`__builtin_classify_type` would be the other way to ask, and its operand is
 * an expression whose volatile read GCC is entitled to emit.) */
#define GABBRO_KMOD_ATOMAR_TYP(P)                                              \
    _Static_assert(_Generic(*(P),                                              \
                            float: 0, double: 0, long double: 0, default: 1),  \
                   "a Gabbro `atomic` of floating-point type has no "          \
                   "kernel-module lowering: kernel code may not use the FPU "  \
                   "without kernel_fpu_begin/end, which nothing here declares")

#define GABBRO_KMOD_ATOMAR_BREITE(P)                                           \
    _Static_assert(sizeof(*(P)) == 4 || sizeof(*(P)) == sizeof(long),          \
                   "a read-modify-write on this `atomic` needs a cmpxchg of "  \
                   "its width, and this mapping selects the target's native "  \
                   "try_cmpxchg only (4 bytes or the machine word). Loads and "\
                   "stores are unaffected")

/* -- load ------------------------------------------------------------------ */
/*
 * The ordering word arrives as a TOKEN and is pasted, so it is not macro
 * expanded first -- which is what makes an unlisted ordering a loud undefined
 * name instead of a silent fallback. (The two-level dance `sperre.h` does next
 * door is for the opposite case: there the argument IS a macro.)
 */
#define atomic_load_explicit(P, O) GABBRO_KMOD_LADEN_##O(P)

#define GABBRO_KMOD_LADEN_memory_order_relaxed(P)                              \
    ({ GABBRO_KMOD_ATOMAR_TYP(P); READ_ONCE(*(P)); })

#define GABBRO_KMOD_LADEN_memory_order_acquire(P)                              \
    ({ GABBRO_KMOD_ATOMAR_TYP(P); smp_load_acquire(P); })

#define GABBRO_KMOD_LADEN_memory_order_seq_cst(P)                              \
    ({                                                                         \
        __unqual_scalar_typeof(*(P)) __gabbro_w;                               \
        GABBRO_KMOD_ATOMAR_TYP(P);                                             \
        smp_mb();                                                              \
        __gabbro_w = smp_load_acquire(P);                                      \
        smp_mb();                                                              \
        __gabbro_w;                                                            \
    })

/* -- store ----------------------------------------------------------------- */

#define atomic_store_explicit(P, V, O) GABBRO_KMOD_LEGEN_##O(P, V)

#define GABBRO_KMOD_LEGEN_memory_order_relaxed(P, V)                           \
    ({ GABBRO_KMOD_ATOMAR_TYP(P); WRITE_ONCE(*(P), (V)); })

#define GABBRO_KMOD_LEGEN_memory_order_release(P, V)                           \
    ({ GABBRO_KMOD_ATOMAR_TYP(P); smp_store_release(P, (V)); })

#define GABBRO_KMOD_LEGEN_memory_order_seq_cst(P, V)                           \
    ({ GABBRO_KMOD_ATOMAR_TYP(P); smp_mb(); smp_store_mb(*(P), (V)); })

/* -- read-modify-write ----------------------------------------------------- */
/*
 * ONE loop for all five fetch forms. The body re-reads nothing: `try_cmpxchg`
 * writes the observed value back into `__gabbro_alt` on a lost race, which is
 * exactly the shape C11 gives the compare-exchange -- so the loop is the
 * kernel's own idiom and not an invention.
 *
 * The initial `READ_ONCE` and every lost race are relaxed reads, and that is
 * sound for any ordering: the operation C11 talks about is the SUCCESSFUL
 * read-modify-write, and the suffix on `CX` carries its ordering.
 */
#define GABBRO_KMOD_RMW(P, OPER, V, CX, VOR, NACH)                             \
    ({                                                                         \
        __unqual_scalar_typeof(*(P)) __gabbro_alt;                             \
        __unqual_scalar_typeof(*(P)) __gabbro_neu;                             \
        GABBRO_KMOD_ATOMAR_TYP(P);                                             \
        GABBRO_KMOD_ATOMAR_BREITE(P);                                          \
        __gabbro_alt = READ_ONCE(*(P));                                        \
        VOR;                                                                   \
        for (;;) {                                                             \
            __gabbro_neu =                                                     \
                (__unqual_scalar_typeof(*(P)))(__gabbro_alt OPER (V));         \
            if (CX((P), &__gabbro_alt, __gabbro_neu))                          \
                break;                                                         \
        }                                                                      \
        NACH;                                                                  \
        __gabbro_alt;                                                          \
    })

#define GABBRO_KMOD_HOL_memory_order_relaxed(P, OPER, V)                       \
    GABBRO_KMOD_RMW(P, OPER, V, try_cmpxchg_relaxed, (void)0, (void)0)
#define GABBRO_KMOD_HOL_memory_order_acq_rel(P, OPER, V)                       \
    GABBRO_KMOD_RMW(P, OPER, V, try_cmpxchg, (void)0, (void)0)
#define GABBRO_KMOD_HOL_memory_order_seq_cst(P, OPER, V)                       \
    GABBRO_KMOD_RMW(P, OPER, V, try_cmpxchg, smp_mb(), smp_mb())

#define atomic_fetch_add_explicit(P, V, O) GABBRO_KMOD_HOL_##O(P, +, V)
#define atomic_fetch_sub_explicit(P, V, O) GABBRO_KMOD_HOL_##O(P, -, V)
#define atomic_fetch_or_explicit(P, V, O)  GABBRO_KMOD_HOL_##O(P, |, V)
#define atomic_fetch_and_explicit(P, V, O) GABBRO_KMOD_HOL_##O(P, &, V)
#define atomic_fetch_xor_explicit(P, V, O) GABBRO_KMOD_HOL_##O(P, ^, V)

/* -- compare-exchange ------------------------------------------------------ */
/*
 * BOTH orderings are pasted, so the table is one row per PAIR. The emitter
 * writes exactly three pairs (`emit.rs`, the ordering table of `atom_target`):
 * (relaxed, relaxed), (release, acquire) and (seq_cst, seq_cst). A fourth pair
 * has no row and stops the build.
 *
 * WEAK AND STRONG SHARE A ROW, and in the sound direction: `try_cmpxchg` never
 * fails spuriously, which meets the contract of the weak form (which MAY) as
 * well as of the strong one (which may not).
 */
#define atomic_compare_exchange_weak_explicit(P, E, D, S, F)                   \
    GABBRO_KMOD_CAS(P, E, D, S, F)
#define atomic_compare_exchange_strong_explicit(P, E, D, S, F)                 \
    GABBRO_KMOD_CAS(P, E, D, S, F)

#define GABBRO_KMOD_CAS(P, E, D, S, F) GABBRO_KMOD_CAS_##S##_##F(P, E, D)

#define GABBRO_KMOD_CAS_memory_order_relaxed_memory_order_relaxed(P, E, D)     \
    ({                                                                         \
        GABBRO_KMOD_ATOMAR_TYP(P);                                             \
        GABBRO_KMOD_ATOMAR_BREITE(P);                                          \
        try_cmpxchg_relaxed((P), (E), (D));                                    \
    })

/* The `smp_mb()` on the failure path is the whole point of this row -- see the
 * file header. Without it the release suffix would leave a failed exchange
 * unordered where C11 asked for an acquire. */
#define GABBRO_KMOD_CAS_memory_order_release_memory_order_acquire(P, E, D)     \
    ({                                                                         \
        bool __gabbro_ok;                                                      \
        GABBRO_KMOD_ATOMAR_TYP(P);                                             \
        GABBRO_KMOD_ATOMAR_BREITE(P);                                          \
        __gabbro_ok = try_cmpxchg_release((P), (E), (D));                      \
        if (!__gabbro_ok)                                                      \
            smp_mb();                                                          \
        __gabbro_ok;                                                           \
    })

#define GABBRO_KMOD_CAS_memory_order_seq_cst_memory_order_seq_cst(P, E, D)     \
    ({                                                                         \
        bool __gabbro_ok;                                                      \
        GABBRO_KMOD_ATOMAR_TYP(P);                                             \
        GABBRO_KMOD_ATOMAR_BREITE(P);                                          \
        smp_mb();                                                              \
        __gabbro_ok = try_cmpxchg((P), (E), (D));                              \
        smp_mb();                                                              \
        __gabbro_ok;                                                           \
    })

#endif
