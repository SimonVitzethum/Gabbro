/* laufzeit/kmodul/include/stdatomic.h -- <stdatomic.h> inside a kernel module,
 * and the module runtime HAS NO MEMORY MODEL OF ITS OWN (server lane, TODO
 * section 0e K7, 2026-09-28).
 *
 * WHAT THIS FILE IS. The emitted prelude asks for `<stdatomic.h>` on every unit,
 * float or not, atomic or not -- so under the kernel's `-nostdinc` something of
 * that name has to exist. For a unit WITHOUT an `atomic` that is all it has to
 * be: the name, and nothing behind it.
 *
 * For a unit WITH one, the table that maps the emitter's nine C11 call forms and
 * one qualifier onto the kernel's own memory model is the PROGRAM's
 * (Simon, 2026-09-28, `AUFTRAG-1.md` K7: *"auch im Programm vom Nutzer"*). It
 * lives in `bibliothek/linux-kmod/stdatomic.h` -- ordinary user code a program
 * names in its manifest, copied into the module's include directory AFTER this
 * file and therefore in place of it. A different kernel, a different memory
 * model, a different table; no third party edits this tree for it.
 *
 * *The table itself did not change when it moved* (K6 wrote it, 2026-09-28, and
 * the named assumption (M11) of `grammatik/Grammatik/Zielsatz/Spec.lean` is
 * about the ROWS and not about the file they stand in -- see
 * `messung/SERVER-0E-SPEC-DIFF.md` section 10).
 *
 * WHY A REFUSAL AND NOT AN EMPTY FILE. `_Atomic` is the one thing an unbound
 * module MUST NOT silently compile: the emitter writes it as a qualifier, and a
 * `#define _Atomic` to nothing would leave every access a PLAIN, UNORDERED one
 * and the module would load, run and answer plausible numbers. So the qualifier
 * pastes to a name nothing declares, and the kernel build stops on it. *Silence
 * is not among the answers* -- the same reading the K6 table gives an unlisted
 * (form, ordering) pair.
 *
 * THIS IS THE SECOND DOOR AND NOT THE FIRST. `gabbro build` refuses a `module`
 * unit that declares an `atomic` and names no `stdatomic.h`, before a byte of C
 * is written (`crates/gabbro-cli/src/bau.rs`, `modulregel`), with the file to
 * add in its own sentence. What is left here is what answers a HAND-WRITTEN
 * `Kbuild` -- the same arrangement the floating-point refusal has, where
 * `bau.rs` speaks first and a `_Generic` in the table speaks last.
 */
#ifndef GABBRO_KMOD_STDATOMIC_H
#define GABBRO_KMOD_STDATOMIC_H

#define _Atomic GABBRO_KMOD_ATOMIC_NICHT_GEBUNDEN_siehe_bibliothek_linux_kmod_stdatomic_h

#endif
