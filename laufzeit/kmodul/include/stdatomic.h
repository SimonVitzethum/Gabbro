/* laufzeit/kmodul/include/stdatomic.h -- and a REFUSAL, not a shim.
 *
 * Every emitted Gabbro unit includes <stdatomic.h> in its prelude, float or
 * not, atomic or not. A unit that declares no `atomic` uses nothing from it,
 * and this file is then the name the prelude asks for and nothing more.
 *
 * A unit that DOES declare an `atomic` is a different matter, and this file
 * refuses it rather than pretending: C11 `_Atomic` is not the kernel's memory
 * model. The kernel has its own (`READ_ONCE`/`WRITE_ONCE`, `atomic_t`,
 * `smp_*` barriers), documented as the thing to use, and a Gabbro atomic
 * lowered to `_Atomic` inside a kernel object would be a second memory model
 * beside it -- with the goal theorem's atomic rely (`GabbroZiel`'s `SchwachX`)
 * proved about the FIRST one. *Silence there would be the worst of the three
 * possible answers*, so the answer is a compile error with this text.
 *
 * What it would take to lift it is named, not hidden: a kernel-module lowering
 * of `atomic` onto the kernel's own primitives, and the argument that the
 * kernel's model refines the one `SchwachX` assumes. Neither is built.
 * Tracked in the report of the server lane (`messung/SERVER-0E-REPORT.md`).
 */
#ifndef GABBRO_KMOD_STDATOMIC_H
#define GABBRO_KMOD_STDATOMIC_H

#define _Atomic GABBRO_KMOD_ATOMIC_NICHT_GETRAGEN
#define atomic_load_explicit(...)  GABBRO_KMOD_ATOMIC_NICHT_GETRAGEN
#define atomic_store_explicit(...) GABBRO_KMOD_ATOMIC_NICHT_GETRAGEN
#define atomic_fetch_add_explicit(...) GABBRO_KMOD_ATOMIC_NICHT_GETRAGEN
#define atomic_compare_exchange_weak_explicit(...) GABBRO_KMOD_ATOMIC_NICHT_GETRAGEN

#endif
