/*
 * stage0/c/syscall.c -- the one piece of handwritten C in stage 0 (a WALL, AGENTS.md §3: "handwritten C or
 * assembly stays only where Gabbro cannot express the thing, each piece with its written reason, booked as a wall").
 *
 * Reason: stage 0 is a Lean executable. Lean has no way to issue a machine `syscall`/`svc` instruction; the program
 * it runs declares its system calls as Gabbro `syscall` gates, and this function is the generic trampoline that
 * issues one: the number and six argument words, one of which may be replaced by the address of a byte buffer
 * (the bytes of a Gabbro byte table, copied in before and back after the call by Lean). Nothing else lives here:
 * no libc call, no policy, no knowledge of any particular system call.
 *
 * The second piece is the world lock of a run on several OS threads (`Tor/Faeden.lean`): one word taken by an
 * atomic compare-and-swap and slept on with the raw `futex` system call, and a generation word the threads wait on
 * until another thread has stepped. Reason: Lean has no compare-and-swap on a machine word and no futex.
 *
 * Named assumption (PLAN-SELF-HOSTING.md §2): the system call does what its Gabbro contract says.
 */
#include <lean/lean.h>
#include <stdint.h>

static long roh(uint64_t nr, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5) {
    long ret;
#if defined(__x86_64__)
    register long r10 __asm__("r10") = (long)a3;
    register long r8 __asm__("r8") = (long)a4;
    register long r9 __asm__("r9") = (long)a5;
    __asm__ volatile("syscall"
                     : "=a"(ret)
                     : "a"(nr), "D"(a0), "S"(a1), "d"(a2), "r"(r10), "r"(r8), "r"(r9)
                     : "rcx", "r11", "memory");
#elif defined(__aarch64__)
    register long x8 __asm__("x8") = (long)nr;
    register long x0 __asm__("x0") = (long)a0;
    register long x1 __asm__("x1") = (long)a1;
    register long x2 __asm__("x2") = (long)a2;
    register long x3 __asm__("x3") = (long)a3;
    register long x4 __asm__("x4") = (long)a4;
    register long x5 __asm__("x5") = (long)a5;
    __asm__ volatile("svc #0"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5)
                     : "memory");
    ret = x0;
#else
#error "stage 0 issues system calls on x86_64 and aarch64 only"
#endif
    return ret;
}

LEAN_EXPORT lean_obj_res gabbro_stage0_syscall(uint64_t nr, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3,
                                               uint64_t a4, uint64_t a5, lean_obj_arg buf, uint8_t which,
                                               lean_obj_arg world) {
    (void)world;
    if (!lean_is_exclusive(buf)) {
        /* lean_copy_sarray takes ownership of its argument (it releases the original) */
        buf = lean_copy_sarray(buf, lean_sarray_capacity(buf));
    }
    uint64_t a[6] = {a0, a1, a2, a3, a4, a5};
    if (which < 6) a[which] = (uint64_t)(uintptr_t)lean_sarray_cptr(buf);
    long ret = roh(nr, a[0], a[1], a[2], a[3], a[4], a[5]);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64((uint64_t)ret));
    lean_ctor_set(pair, 1, buf);
    return lean_io_result_mk_ok(pair);
}

#if defined(__x86_64__)
#define SYS_FUTEX 202
#elif defined(__aarch64__)
#define SYS_FUTEX 98
#endif
#define FUTEX_WAIT_PRIVATE 128
#define FUTEX_WAKE_PRIVATE 129

/* 0 free, 1 held, 2 held with sleepers (the three-state futex lock) */
static uint32_t welt_schloss = 0;
/* counts the steps taken; a thread that cannot step sleeps until it moves */
static uint32_t welt_generation = 0;
/* the threads sleeping on the generation: a step wakes only when there are some */
static uint32_t welt_wartende = 0;

LEAN_EXPORT lean_obj_res gabbro_stage0_nimm(lean_obj_arg world) {
    (void)world;
    uint32_t c = 0;
    if (!__atomic_compare_exchange_n(&welt_schloss, &c, 1, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED)) {
        if (c != 2) c = __atomic_exchange_n(&welt_schloss, 2, __ATOMIC_ACQUIRE);
        while (c != 0) {
            roh(SYS_FUTEX, (uint64_t)(uintptr_t)&welt_schloss, FUTEX_WAIT_PRIVATE, 2, 0, 0, 0);
            c = __atomic_exchange_n(&welt_schloss, 2, __ATOMIC_ACQUIRE);
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res gabbro_stage0_gib(lean_obj_arg world) {
    (void)world;
    if (__atomic_exchange_n(&welt_schloss, 0, __ATOMIC_RELEASE) == 2)
        roh(SYS_FUTEX, (uint64_t)(uintptr_t)&welt_schloss, FUTEX_WAKE_PRIVATE, 1, 0, 0, 0);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res gabbro_stage0_generation(lean_obj_arg world) {
    (void)world;
    return lean_io_result_mk_ok(lean_box_uint32(__atomic_load_n(&welt_generation, __ATOMIC_ACQUIRE)));
}

LEAN_EXPORT lean_obj_res gabbro_stage0_warte(uint32_t g, lean_obj_arg world) {
    (void)world;
    /* announce first, then sleep only while the generation is still g (the kernel checks it atomically) */
    __atomic_add_fetch(&welt_wartende, 1, __ATOMIC_SEQ_CST);
    if (__atomic_load_n(&welt_generation, __ATOMIC_SEQ_CST) == g)
        roh(SYS_FUTEX, (uint64_t)(uintptr_t)&welt_generation, FUTEX_WAIT_PRIVATE, g, 0, 0, 0);
    __atomic_sub_fetch(&welt_wartende, 1, __ATOMIC_SEQ_CST);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res gabbro_stage0_wecke(lean_obj_arg world) {
    (void)world;
    __atomic_add_fetch(&welt_generation, 1, __ATOMIC_SEQ_CST);
    /* a sleeper announced before this load sees the new generation or is woken here */
    if (__atomic_load_n(&welt_wartende, __ATOMIC_SEQ_CST) != 0)
        roh(SYS_FUTEX, (uint64_t)(uintptr_t)&welt_generation, FUTEX_WAKE_PRIVATE, 0x7fffffff, 0, 0, 0);
    return lean_io_result_mk_ok(lean_box(0));
}
