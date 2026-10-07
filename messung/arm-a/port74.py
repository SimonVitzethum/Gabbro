import os
import re
S = os.environ["ARM_A_SCRATCH"] + "/"
t = open(S + "em0/74-syscall-schreiben.c").read()
# hand-port of the ONE stub: x86_64 Linux write (number 1; rdi,rsi,rdx; rax) -> AArch64 Linux write (number 64; x0,x1,x2,x8; x0)
t = t.replace('register uint64_t _sys_rdi __asm__("rdi")', 'register uint64_t _sys_rdi __asm__("x0")')
t = t.replace('register uint64_t _sys_rsi __asm__("rsi")', 'register uint64_t _sys_rsi __asm__("x1")')
t = t.replace('register uint64_t _sys_rdx __asm__("rdx")', 'register uint64_t _sys_rdx __asm__("x2")')
t = t.replace('register int64_t _sys_rax __asm__("rax") = (int64_t)1u;', 'register int64_t _sys_nr __asm__("x8") = (int64_t)64u;')
t = t.replace('''        "syscall\\n"
        : "+a" (_sys_rax)
        : "r" (_sys_rdi), "r" (_sys_rsi), "r" (_sys_rdx)
        : "rcx", "r11", "memory");''', '''        "svc #0\\n"
        : "+r" (_sys_rdi)
        : "r" (_sys_rsi), "r" (_sys_rdx), "r" (_sys_nr)
        : "memory");
    int64_t _sys_rax = (int64_t)_sys_rdi;''')
open(S + "em0/74-ported.c", "w").write(t)
open(S + "drv74.c", "w").write('''#include <stdio.h>
#include "74-ported.c"
int main(void) {
    static const char msg[3] = {'o', 'k', '\\n'};
    uint64_t n = schreibe(1, (uint64_t)msg, 3);
    printf("%llu\\n", (unsigned long long)n);
    return 0;
}
''')
