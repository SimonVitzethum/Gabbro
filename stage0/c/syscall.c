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
 * Named assumption (PLAN-SELF-HOSTING.md §2): the system call does what its Gabbro contract says.
 */
#include <lean/lean.h>
#include <stdint.h>

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
    long ret;
#if defined(__x86_64__)
    register long r10 __asm__("r10") = (long)a[3];
    register long r8 __asm__("r8") = (long)a[4];
    register long r9 __asm__("r9") = (long)a[5];
    __asm__ volatile("syscall"
                     : "=a"(ret)
                     : "a"(nr), "D"(a[0]), "S"(a[1]), "d"(a[2]), "r"(r10), "r"(r8), "r"(r9)
                     : "rcx", "r11", "memory");
#elif defined(__aarch64__)
    register long x8 __asm__("x8") = (long)nr;
    register long x0 __asm__("x0") = (long)a[0];
    register long x1 __asm__("x1") = (long)a[1];
    register long x2 __asm__("x2") = (long)a[2];
    register long x3 __asm__("x3") = (long)a[3];
    register long x4 __asm__("x4") = (long)a[4];
    register long x5 __asm__("x5") = (long)a[5];
    __asm__ volatile("svc #0"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5)
                     : "memory");
    ret = x0;
#else
#error "stage 0 issues system calls on x86_64 and aarch64 only"
#endif
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64((uint64_t)ret));
    lean_ctor_set(pair, 1, buf);
    return lean_io_result_mk_ok(pair);
}
