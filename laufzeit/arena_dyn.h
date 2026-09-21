/* laufzeit/arena_dyn.h -- reservation/commit runtime for dynamic arenas (wave D).
 *
 * WHAT THIS IS. A dynamic arena declares a static ceiling `max M` (address
 * reserved, never touched implicitly) and a committed prefix `committed`
 * (`hi <= committed <= M`) grown explicitly by `grow`. This header is the
 * OS-free side of that split: the descriptor the program carries and the
 * two functions behind it. Every OS fact (page size, reserve/commit calls,
 * first-touch policy) lives strictly inside `laufzeit/arena_dyn.c`.
 *
 * WHY A RUNTIME AND NOT EMITTED C. Reservation is the runtime's, not the
 * program's: the goal theorem books it as assumption (d) `Laufzeit`
 * (`grammatik/Grammatik/Zielsatz/Spec.lean`), the same shelf `laufzeit/`
 * `start.c` stands on. A generator that printed the reserve call into the
 * unit would move a runtime fact into the program text.
 *
 * BINDING CONSTRAINT (owner): no language feature hard-depends on an OS.
 * The descriptor addresses the runtime by declaration data -- slot counts
 * (`max`, `floor_hi`, `used`, `committed`) and the element size from the
 * declaration's element type -- never by an ABI constant. No syscall
 * number, no `MAP_*` here; the mechanical guard is
 * `instrumente/pruefe-osfrei.py`.
 */

#ifndef GABBRO_ARENA_DYN_H
#define GABBRO_ARENA_DYN_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Named exits: a refused load is a number, not a silence. `grow` below the
 * ceiling reports through its return value (the program's `else` branch);
 * only the load refusal exits, because there is no program running yet to
 * take a branch. */
#define GABBRO_ARENA_EXIT_RESERVE 3

/* The descriptor the program carries (PLAN-DYNAMISCH.md section 6: the
 * emitter passes a pointer to this, never sizes, never addresses, never
 * flags). `used` is the allocation cursor the emitted `alloc` bumps (as
 * today); `committed` is the usable prefix, initialised to `floor_hi` and
 * bumped only by `gabbro_arena_grow`. */
typedef struct {
    void *base;          /* reserved region base, set at load by reserve */
    uint32_t elem;       /* slot size in bytes, from the element type */
    uint32_t max;        /* ceiling M: compile-time count, reserved */
    uint32_t floor_hi;   /* commit floor hi: initially committed count */
    uint32_t used;       /* allocation cursor since the last reset */
    uint32_t committed;  /* committed prefix: hi <= committed <= max */
} gabbro_arena_desc;

/* Reserve the virtual range for `d->max` slots before any start runs.
 * Establishes `base`; leaves `used` at zero and `committed` at `floor_hi`.
 * A failed reservation refuses the load: message on stderr plus
 * `exit(GABBRO_ARENA_EXIT_RESERVE)`. It never starts a program with a
 * smaller range, and it never returns a null base. */
void gabbro_arena_reserve(gabbro_arena_desc *d);

/* Commit `n` more slots below `max`: on success bump `committed` and
 * return true (the new slots read as zero); when the platform refuses the
 * commit below `max` return false and leave `committed` unchanged -- the
 * caller runs the `else` branch. On hosted Linux the commit is lazy and a
 * refusal comes only under strict overcommit accounting; with the default
 * heuristic, out of memory surfaces at first touch as the OOM killer, not
 * as `false` (see `arena_dyn.c`). A request reaching past `max`
 * fail-stops, because a silent partial commit would be the unnamed gap
 * this split exists to close. The checker (`N426`, fix lane F2) holds every
 * `grow` against the upper bound of what the whole run may commit, so an
 * accepted unit reaches that stop only outside the checked run model (a
 * routine entered again by a caller the unit does not see). */
bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n);

#endif
