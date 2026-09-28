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

/* -- the RUN-TIME `start`: the raw kernel thread ---------------------------- */
/*
 * **THIS IS THE ONLY PLACE A `syscall` INSTRUCTION STANDS IN A HOSTED GABBRO
 * BUILD**, and it is a file of the PROGRAM. It used to stand in
 * `laufzeit/faden.c`, where `instrumente/pruefe-os-bindung.sh` counted it as
 * three SITES (`MARKE_ROHRUF`) -- because a raw system call leaves no undefined
 * symbol, so the symbol stage is blind to it and a runtime could have hidden its
 * whole Linux dependency in assembly.
 *
 * SIMON'S RULE, AS CODE, unchanged by the move: threads at run time are made by
 * OUR OWN code issuing the kernel system call -- not by libc
 * (`pthread_create`, the glibc `clone()` wrapper, `fork`). The `pthread_create`
 * above is the DRIVER's thread, started once before the program runs; this is
 * the `start { f };` statement of a running Gabbro function, and it keeps the
 * raw call it always had. *Both are the program's now, and they differ in the
 * primitive because they differ in the question.*
 *
 * REGISTERS, ONE BY ONE. The `syscall` instruction itself destroys `rcx` (it
 * holds the return address) and `r11` (it holds the flags) -- both stand in
 * every clobber list below, the same two the syscall stub destroys (`emit.rs`,
 * `syscall_stumpf`). The kernel calling convention takes the number in `rax`,
 * arguments in `rdi rsi rdx r10 r8 r9`, the answer in `rax`. `r10` has no
 * constraint letter, so it travels in a pinned register variable (the musl idiom
 * the stub already uses).
 *
 * FLAGS, ONE BY ONE. The clone set is
 *
 *   CLONE_VM         0x00000100  one address space: the threads share the
 *                                tables, which is what makes them threads.
 *   CLONE_FS         0x00000200  one filesystem view (like the glibc wrapper).
 *   CLONE_FILES      0x00000400  one file table (like the glibc wrapper).
 *   CLONE_SIGHAND    0x00000800  one signal-handler table (like the wrapper).
 *   CLONE_THREAD     0x00010000  one thread group: signals address the group,
 *                                and `exit` below ends THIS thread, not the
 *                                process (that is why it must not be
 *                                `exit_group`).
 *   CLONE_SYSVSEM    0x00040000  one SysV semaphore undo list (wrapper parity;
 *                                Gabbro's own locks are futexes, never SysV).
 *   CLONE_PARENT_SETTID  0x00100000  the kernel stores the child's TID into
 *                                the join word BEFORE the child can run -- the
 *                                FIRST of the three promises `laufzeit/bindung.h`
 *                                names, and the runtime's loop rests on it.
 *   CLONE_CHILD_CLEARTID 0x00200000  the join: the kernel clears the word at
 *                                `ctid` on thread exit and wakes one futex
 *                                waiter, so the join is a wait loop and not a
 *                                guess about scheduling. It is also the SECOND
 *                                promise -- the clear happens-before what the
 *                                waiter reads.
 *
 * What is NOT set, and why:
 *
 *   CLONE_SETTLS is absent: no TLS is used anywhere on these paths. The threads
 *   run nullary roots over shared tables plus their own stack; they touch no
 *   `errno` (raw answers stay in locals), no thread-local, nothing that would
 *   need a segment base. Setting it would promise a facility nobody reads.
 *
 *   CLONE_PARENT_SETTID WAS absent until 2026-09-26, and that was a lost join:
 *   the parent stored the TID into the word itself, AFTER `clone` returned --
 *   and a child that ran to its end first had its word cleared by the kernel
 *   BEFORE that store, which then wrote a dead TID back. The join then waited on
 *   it forever. Measured by Opus agent I: 200000 start/join rounds of an empty
 *   root on one stack hung (timeout) before round 20000; with the flag, the
 *   kernel writes the TID in `copy_process`, before `wake_up_new_task`, so the
 *   word says "alive" before the child can end, and the same probe runs through
 *   (`instrumente/pruefe-metall.sh`, hosted counter-probe). The bare-metal
 *   runtime keeps the same order by construction (`laufzeit/metall/kern.c`,
 *   `faden_anlegen`).
 *
 * THE CHILD NEVER EXECUTES A C FRAME ON THE NEW STACK. `clone` returns twice --
 * once in the parent (the TID), once in the child (zero) -- but the kernel puts
 * the handed stack under the child AT the return: the very next C instruction
 * (`pop %rbp; ret` of a helper call) would pop words off the NEW stack and
 * return into whatever they hold (a zeroed static stack holds zero -- measured
 * 2026-09-26 as a jump to NULL). So the `syscall` is issued from inline asm that
 * branches BEFORE any C stack operation: the child moves the handed top into
 * `rsp` (already there -- the move states the ownership), CALLS the root on it,
 * and when the root returns exits the THREAD with `SYS_exit` (60), never
 * `exit_group` (231). A `call` pushes its return address onto the NEW stack, so
 * that push is the first word the new stack carries and the whole root runs
 * where the unit said it would. `ud2` stands behind the exit the way the stub's
 * hardware outcome stands behind its decoding: under the kernel contract that
 * point is not reached, and the instruction says so loudly instead of falling
 * through.
 *
 * NO `errno`. Raw answers stay negative in locals and come back positive;
 * nothing here names the thread-local error cell, which is exactly the TLS the
 * flags above declined -- and it is why this file's `<stdio.h>` and `<stdlib.h>`
 * above are the REPORT channel's business and not this one's.
 *
 * MACHINE. x86_64 Linux only, like the syscall stub. Every number below is the
 * kernel's, read from the architecture's ABI and never from a libc header.
 */

#define GABBRO_SYS_CLONE 56L
#define GABBRO_SYS_FUTEX 202L
#define GABBRO_FUTEX_WAIT 0L

#define GABBRO_CLONE_VM 0x00000100L
#define GABBRO_CLONE_FS 0x00000200L
#define GABBRO_CLONE_FILES 0x00000400L
#define GABBRO_CLONE_SIGHAND 0x00000800L
#define GABBRO_CLONE_THREAD 0x00010000L
#define GABBRO_CLONE_SYSVSEM 0x00040000L
#define GABBRO_CLONE_PARENT_SETTID 0x00100000L
#define GABBRO_CLONE_CHILD_CLEARTID 0x00200000L

#define GABBRO_CLONE_FLAGS \
    (GABBRO_CLONE_VM | GABBRO_CLONE_FS | GABBRO_CLONE_FILES | GABBRO_CLONE_SIGHAND | \
     GABBRO_CLONE_THREAD | GABBRO_CLONE_SYSVSEM | GABBRO_CLONE_PARENT_SETTID | \
     GABBRO_CLONE_CHILD_CLEARTID)

/* One raw system call.
 *
 * WHY SIX ARGUMENTS ALWAYS. The sites here pass at most four; spelling all six
 * keeps ONE helper with one clobber list instead of four shapes that drift
 * apart (the same reason the stub template is one template).
 */
static long roh_aufruf(long nr, long a1, long a2, long a3, long a4, long a5, long a6)
{
    register long r10 __asm__("r10") = a4;
    register long r8 __asm__("r8") = a5;
    register long r9 __asm__("r9") = a6;
    register long rax __asm__("rax") = nr;
    __asm__ __volatile__(
        "syscall"
        : "+a"(rax)
        : "D"(a1), "S"(a2), "d"(a3), "r"(r10), "r"(r8), "r"(r9)
        : "memory", "rcx", "r11", "cc");
    return rax;
}

uint32_t gabbro_os_klon(uint64_t koerper, uint64_t spitze, uint64_t wort)
{
    long r;
    /* rdi = flags, rsi = handed stack, rdx = ptid (the join word: the kernel
     * sets it to the TID before the child runs), r10 = ctid (the join word the
     * kernel clears), r8 = tls (none: no CLONE_SETTLS). The pins are the musl
     * idiom the syscall stub uses (`r10` has no constraint letter); `rax` is
     * in-out (`+a`): the number going in, the raw answer coming out. */
    register long r_rax __asm__("rax") = GABBRO_SYS_CLONE;
    register long r_rdi __asm__("rdi") = GABBRO_CLONE_FLAGS;
    register long r_rsi __asm__("rsi") = (long)(uintptr_t)spitze;
    register long r_rdx __asm__("rdx") = (long)(uintptr_t)wort;
    register long r_r10 __asm__("r10") = (long)(uintptr_t)wort;
    register long r_r8 __asm__("r8") = 0;
    /* The runtime checked the three for null and the stack top for alignment
     * before it asked (`laufzeit/faden.c`); this is the binding's own floor, so
     * that a body called from anywhere else still refuses rather than clones
     * onto address zero. */
    if (koerper == 0 || spitze == 0 || wort == 0) {
        return 22; /* EINVAL */
    }
    __asm__ __volatile__(
        "syscall\n\t"
        "testq %%rax, %%rax\n\t"
        "jnz 1f\n\t"
        "movq %[spitze], %%rsp\n\t"
        "call *%[fn]\n\t"
        "movl $60, %%eax\n\t"
        "xorl %%edi, %%edi\n\t"
        "syscall\n\t"
        "ud2\n\t"
        "1:\n\t"
        : "+a"(r_rax)
        : "r"(r_rdi), "r"(r_rsi), "r"(r_rdx), "r"(r_r10), "r"(r_r8),
          [spitze] "r"((long)(uintptr_t)spitze), [fn] "r"((long)(uintptr_t)koerper)
        : "memory", "rcx", "r11", "cc");
    r = r_rax;
    if (r < 0) {
        long e = -r;
        return e > 4095 ? 12u : (uint32_t)e; /* ENOMEM where the number is wild. */
    }
    return 0;
}

void gabbro_os_wort_warte(uint64_t wort, uint32_t erwartet)
{
    /* FUTEX_WAIT blocks only while the word still holds the seen value: a clear
     * racing the caller's load fails with EAGAIN, a spurious wake simply
     * returns. Both are legal answers here -- the runtime's loop re-reads and
     * never trusts this call (`laufzeit/faden.c`). */
    (void)roh_aufruf(GABBRO_SYS_FUTEX, (long)(uintptr_t)wort, GABBRO_FUTEX_WAIT,
                     (long)erwartet, 0, 0, 0);
}
