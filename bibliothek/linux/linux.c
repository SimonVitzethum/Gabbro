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
 * `laufzeit/arena_dyn.c`; and, in the GENERATED DRIVER, `pthread_create`,
 * `pthread_join`, `pthread_mutex_lock`, `pthread_mutex_unlock`, `pause` and the
 * `fprintf`/`abort` of its error paths. Eleven names, and they are all below
 * now -- the symbol mark reads 0.
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
#include <string.h>
#include <unistd.h>
#include <pthread.h>
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
    case GABBRO_OS_M_START:
        fprintf(stderr,
                "gabbro: declared start %llu did not start (error %llu)\n",
                (unsigned long long)a, (unsigned long long)b);
        break;
    case GABBRO_OS_M_WARTE:
        fprintf(stderr,
                "gabbro: declared start %llu was not joined (error %llu)\n",
                (unsigned long long)a, (unsigned long long)b);
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

/* -- the generated driver's locks ------------------------------------------ */
/*
 * WHY THE C LIBRARY'S TYPE LIVES ON THIS SIDE. A `pthread_mutex_t` is as much
 * the library's as `pthread_mutex_lock` is, and its size is the library's
 * business -- it differs between glibc and musl and between word sizes. So the
 * driver hands over a blob of words and this file lays the library's own type
 * into it, with a `_Static_assert` held against the very library the program is
 * being built against. *A blob too small is a loud build error and never a
 * silent overrun.*
 *
 * DEFAULT ATTRIBUTES, AND THAT IS THE POINT. A NORMAL mutex, not a recursive
 * one: a recursive mutex would let one thread take a Gabbro `lock` twice and
 * pass, which is exactly the rank discipline the checker enforces -- the
 * assumption `os_bindung_faden` of `linux.gab` is where that promise is named.
 */
_Static_assert(sizeof(pthread_mutex_t)
                   <= GABBRO_OS_SPERRE_WORTE * sizeof(uint64_t),
               "this C library's pthread_mutex_t does not fit the runtime's lock blob "
               "-- raise GABBRO_OS_SPERRE_WORTE in laufzeit/bindung.h");
_Static_assert(_Alignof(pthread_mutex_t) <= _Alignof(uint64_t),
               "this C library's pthread_mutex_t wants more alignment than the runtime's "
               "lock blob has");

static pthread_mutex_t *sperre(uint64_t s)
{
    return (pthread_mutex_t *)(uintptr_t)s;
}

/*
 * **A lock operation that fails ends the program**, and the three of them do it
 * here rather than answering a code. The driver has no `else` at a lock it must
 * hold: a `L_nimm` that returned without the lock would run a critical section
 * unprotected, which is the one outcome worse than stopping. The words are on
 * this side anyway.
 */
static void sperre_stop(const char *was, int rc)
{
    fprintf(stderr, "gabbro: %s: %d\n", was, rc);
    gabbro_os_ende(GABBRO_OS_ENDE_ABBRUCH);
}

void gabbro_os_sperre_init(uint64_t s)
{
    int rc;

    memset(sperre(s), 0, sizeof(pthread_mutex_t));
    rc = pthread_mutex_init(sperre(s), NULL);
    if (rc != 0) {
        sperre_stop("lock init", rc);
    }
}

void gabbro_os_sperre_nimm(uint64_t s)
{
    int rc = pthread_mutex_lock(sperre(s));

    if (rc != 0) {
        sperre_stop("lock acquire", rc);
    }
}

void gabbro_os_sperre_gib(uint64_t s)
{
    int rc = pthread_mutex_unlock(sperre(s));

    if (rc != 0) {
        sperre_stop("lock release", rc);
    }
}

/* -- the generated driver's threads ---------------------------------------- */
/*
 * THE ADAPTER IS HERE BECAUSE THE SIGNATURE IS. `pthread_create` wants
 * `void *(*)(void *)` and an emitted Gabbro root is `void (*)(void)`; the
 * driver used to carry one wrapper per root for exactly that reason, and with
 * the POSIX name gone from the driver the wrapper belongs where the POSIX
 * signature is. One adapter for every root, because the root travels in the
 * blob.
 *
 * `gestartet` AND WHY A FAILED START MUST STILL BE WAITABLE. The driver's error
 * path joins every root it started before the failure and then returns 2; a
 * blob that a failed `pthread_create` left unjoinable would either hang the
 * program in `pthread_join` or be undefined behaviour on a thread id nobody
 * set. So the flag is written before the start is attempted and read by the
 * wait, and a wait on a blob that never started is a no-op that answers 0.
 */
struct gabbro_os_faden {
    pthread_t faden;
    int gestartet;
};

_Static_assert(sizeof(struct gabbro_os_faden)
                   <= GABBRO_OS_FADEN_WORTE * sizeof(uint64_t),
               "this C library's pthread_t does not fit the runtime's thread blob "
               "-- raise GABBRO_OS_FADEN_WORTE in laufzeit/bindung.h");
_Static_assert(_Alignof(struct gabbro_os_faden) <= _Alignof(uint64_t),
               "this C library's pthread_t wants more alignment than the runtime's "
               "thread blob has");

static struct gabbro_os_faden *faden(uint64_t f)
{
    return (struct gabbro_os_faden *)(uintptr_t)f;
}

/*
 * The root's address crosses as a number, so it crosses back through a union:
 * C converts between an object pointer and a function pointer only as a
 * conditionally supported extension, and a union makes the reinterpretation the
 * thing it actually is instead of a cast the compiler may warn about.
 */
union gabbro_os_wurzel {
    uintptr_t zahl;
    void (*ruf)(void);
};

static void *gabbro_os_faden_lauf(void *p)
{
    union gabbro_os_wurzel w;

    w.zahl = (uintptr_t)p;
    w.ruf();
    return NULL;
}

uint32_t gabbro_os_faden_start(uint64_t f, uint64_t koerper)
{
    int rc;

    memset(faden(f), 0, sizeof(struct gabbro_os_faden));
    rc = pthread_create(&faden(f)->faden, NULL, gabbro_os_faden_lauf,
                        (void *)(uintptr_t)koerper);
    if (rc != 0) {
        return (uint32_t)rc;
    }
    faden(f)->gestartet = 1;
    return 0;
}

uint32_t gabbro_os_faden_warte(uint64_t f)
{
    if (faden(f)->gestartet == 0) {
        return 0;
    }
    return (uint32_t)pthread_join(faden(f)->faden, NULL);
}
