/* bibliothek/linux/linux.c -- THE BODIES of the six primitives `linux.gab`
 * declares (server lane, TODO section 0e K8, 2026-09-28).
 *
 * **THIS FILE IS THE ONE PLACE A POSIX FUNCTION IS NAMED FOR THE BOUNDED
 * HEAP**, and it is a file of the PROGRAM: a manifest lists it, the program's
 * own build compiles it, and whoever wants a different operating system writes
 * a different one. The runtime around it names none of these functions --
 * `laufzeit/bindung.h` declares what the runtime calls and defines nothing.
 * That is Simon's binding constraint of 2026-09-27, *"API calls are always
 * user-made"*, drawn for the runtimes on 2026-09-28: *"an die Hardware ist OK,
 * OS nicht, das muss selbst gemacht werden"*.
 *
 * What stood in the runtime before K8 -- measured, not remembered
 * (`instrumente/pruefe-os-bindung.sh`): `mmap` and `mprotect` for the
 * reservation and each commit, `sysconf` for the page size, and
 * `fprintf`/`exit`/`abort` for the fail-stops, all out of
 * `laufzeit/arena_dyn.c`. Six names, and they are all below now.
 *
 * WHY `PROT_NONE` AND THEN `mprotect`, and not a plain writable mapping: the
 * reservation is ADDRESS SPACE WITHOUT STORAGE -- 32 GiB of it costs page-table
 * entries and nothing else -- and the commit is what makes a prefix usable. The
 * runtime's arithmetic depends on nothing else about the primitive, which is why
 * the module flavour can answer the same three calls out of a budget
 * (`bibliothek/linux-kmod/`) and the numbers above it do not move.
 *
 * WHY NOTHING HERE SCRUBS, and why that is an assumption with a name. A private
 * anonymous mapping reads as zero until written, so a freshly committed slot is
 * zero without a store -- which the bounded heap relies on and does not check
 * (`linux.gab`, `os_bindung_null`). A binding that handed back recycled storage
 * would break exactly that and nothing else visible, so it is named apart from
 * the ABI assumption rather than folded into it.
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/mman.h>

/* The interface, so that every definition below is held against the
 * declaration the runtime calls -- and, through the emitted unit's prototypes,
 * against what the program declared in Gabbro. */
#include "bindung.h"

/* -- the report channel ---------------------------------------------------- */
/*
 * One sentence per code. The runtime hands over a number because printing is an
 * OS call; the WORDS are the program's, and this is where they stand. The
 * sentences are the ones `arena_dyn.c` printed itself until K8 -- kept to the
 * letter, so that a corpus reading a fail-stop's text reads the same text.
 *
 * A code this binding does not know is still reported: a silent drop would make
 * a fail-stop look like an ordinary end.
 */
void gabbro_os_melden(uint32_t code, uint64_t a, uint64_t b)
{
    switch (code) {
    case GABBRO_OS_M_DESKRIPTOR:
        fprintf(stderr,
                "gabbro: arena reserve refused: bad descriptor "
                "(max=%llu floor=%llu)\n",
                (unsigned long long)a, (unsigned long long)b);
        break;
    case GABBRO_OS_M_SPANNE:
        fprintf(stderr,
                "gabbro: arena reserve refused: max=%llu elem=%llu "
                "overflows size_t\n",
                (unsigned long long)a, (unsigned long long)b);
        break;
    case GABBRO_OS_M_RESERVE:
        fprintf(stderr,
                "gabbro: arena reserve refused: cannot reserve %llu slots "
                "(%llu bytes)\n",
                (unsigned long long)a, (unsigned long long)b);
        break;
    case GABBRO_OS_M_BODEN:
        fprintf(stderr,
                "gabbro: arena reserve refused: cannot commit floor %llu\n",
                (unsigned long long)a);
        break;
    case GABBRO_OS_M_UEBER_MAX:
        fprintf(stderr,
                "gabbro: arena grow refused: %llu committed past max %llu\n",
                (unsigned long long)a, (unsigned long long)b);
        break;
    case GABBRO_OS_M_SEITE:
        fprintf(stderr,
                "gabbro: arena runtime: the page size is not answerable (%llu)\n",
                (unsigned long long)a);
        break;
    default:
        fprintf(stderr, "gabbro: runtime fail-stop, code %u (%llu, %llu)\n",
                (unsigned)code, (unsigned long long)a, (unsigned long long)b);
        break;
    }
}

/*
 * **This never returns**, and the declaration in `linux.gab` cannot say so --
 * the runtime therefore writes a fail-closed line behind every call site
 * (`laufzeit/bindung.h`). `GABBRO_OS_ENDE_ABBRUCH` is where the runtime called
 * `abort()`: `_exit` with the status a shell reports for `SIGABRT` keeps the
 * number a corpus reads and drops the core dump, which is noise in a test run
 * and not a diagnosis anybody used.
 */
void gabbro_os_ende(uint32_t code)
{
    fflush(NULL);
    _exit((int)code);
}

/* -- the bounded heap's storage -------------------------------------------- */

uint64_t gabbro_os_reserve(uint64_t bytes)
{
    void *base;

    if (bytes == 0 || (uint64_t)(size_t)bytes != bytes) {
        return 0;
    }
    base = mmap(NULL, (size_t)bytes, PROT_NONE,
                MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED) {
        return 0;
    }
    return (uint64_t)(uintptr_t)base;
}

uint32_t gabbro_os_commit(uint64_t basis, uint64_t versatz, uint64_t bytes)
{
    if (basis == 0 || bytes == 0) {
        return 1;
    }
    if (mprotect((void *)(uintptr_t)(basis + versatz), (size_t)bytes,
                 PROT_READ | PROT_WRITE) != 0) {
        /* The platform refused the commit below the ceiling. The runtime
         * leaves `committed` where it was and the program takes the `else` it
         * wrote beside its `grow`; see `arena_dyn.c` for when this branch is
         * reachable at all (strict overcommit accounting, and there alone). */
        return 1;
    }
    return 0;
}

uint64_t gabbro_os_seitengroesse(void)
{
    long s = sysconf(_SC_PAGESIZE);

    /* 0 is the refusal, and the runtime fail-stops on it rather than guessing:
     * a wrong granularity would make every commit a partial one. */
    return s > 0 ? (uint64_t)s : 0;
}
