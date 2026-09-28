/* laufzeit/kmodul/kmodul.h -- what the kernel-module runtime adds to
 * `laufzeit/arena_dyn.h` (server lane, TODO section 0e H2/K4).
 *
 * Two functions, and both exist because a module is LOADED and UNLOADED
 * rather than started and ended:
 *
 *   gabbro_arena_ladefehler()        did any reservation refuse? A module
 *                                    whose reservation failed must not load:
 *                                    the hosted contract is "never a program
 *                                    started with a smaller range", and in a
 *                                    module the answer to that is a non-zero
 *                                    return out of `module_init`.
 *   gabbro_arena_alles_freigeben()   give every mapped region back. A process
 *                                    exit does this for the hosted runtime and
 *                                    a power-off does it on metal; a module
 *                                    has to say it.
 */
#ifndef GABBRO_KMODUL_H
#define GABBRO_KMODUL_H

int gabbro_arena_ladefehler(void);
void gabbro_arena_alles_freigeben(void);

#endif
