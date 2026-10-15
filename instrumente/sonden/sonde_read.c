/* sonde_read -- the falsifier for `linux_read_contract`.
 *
 * THE OBLIGATION, as it stands in the source (`beispiele/150-fd-lesen.gab`):
 *
 *     assume linux_read_contract
 *         "Read keeps its contract on this machine: at most len bytes, the bytes that stood there, the mapped errnos."
 *         falsifier sonde_read;
 *
 * and at the syscall resting on it (`gate_read`, `abi linux arch x86_64 number 0`,
 * `regs in { rdi = fd, rsi = buf, rdx = len }`,
 * `errors { EBADF => BadFd, EINTR => Interrupted, EINVAL => Invalid }`,
 * `requires len <= MAXLEN, len <= lenof(buf)`, `ensures result <= len`,
 * `effects { writes buf }`).
 *
 * This probe belongs to EXACTLY this one obligation (N024). It was written by fix lane F5
 * (review G04 F4, 2026-09-22): until then the gate borrowed `linux_write_contract`, whose
 * probe only ever wrote.
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * The probe calls the same number the gate's stub loads (raw `syscall(0, ...)`: `rax = 0`,
 * fd in `rdi`, buffer in `rsi`, length in `rdx`), against a pipe -- a probe opens no user
 * files:
 *
 *   1. the frame: with 1024 bytes waiting and `len = 64`, the answer is at most 64
 *      (`ensures result <= len`), the bytes are the ones written, and the guard bytes
 *      behind the 64-byte window are untouched (the kernel stays inside `writes buf` when
 *      `len <= lenof(buf)` -- the bound `N463` decides at the call);
 *   2. `EBADF` on a closed descriptor;
 *   3. `EINVAL` on an `eventfd` read shorter than its 8-byte counter;
 *   4. the end of the stream: a drained pipe with its write end closed answers 0.
 *
 * What it does NOT assert: `EINTR` (no signal stands on this bench -- that arm is held by
 * shape, `N067`), timing, and any descriptor but a pipe and an eventfd.
 *
 * POSITIVE CONTROL (R14)
 * ----------------------
 * `--kaputt` demands the wrong answer on leg 1 (a count ABOVE the window) and must exit 1.
 *
 * Documented runs (cc -std=c11 -O2 -Wall -Wextra -Werror, x86_64 Linux, 2026-09-22):
 *   $ ./sonde_read            -> exit 0 (PASSES)
 *   $ ./sonde_read --kaputt   -> exit 1 (control FALLS)
 *
 * Contract (`sonden/README.md`):
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no Linux x86_64 userland on this machine
 */
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define KOPF "sonde sonde_read :: linux_read_contract (beispiele/150-fd-lesen.gab)\n"

#if !defined(__linux__) || !defined(__x86_64__)
int main(void)
{
    printf(KOPF);
    printf("      no Linux x86_64 userland on this machine -- not runnable here\n");
    return 77;
}
#else
#include <sys/eventfd.h>

#define FENSTER 64
#define WACHE 64
#define VORRAT 1024

/* The gate's own call: number 0, three argument registers. */
static long lies(int fd, void *puffer, unsigned long laenge)
{
    return syscall(0, fd, puffer, laenge);
}

int main(int argc, char **argv)
{
    int kaputt = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--kaputt") == 0) {
            kaputt = 1;
        } else if (strcmp(argv[i], "--runden") == 0 && i + 1 < argc) {
            i++;
        } else if (argv[i][0] >= '0' && argv[i][0] <= '9') {
            /* the runner passes its round count bare */
        } else {
            printf(KOPF);
            printf("      misuse: unknown argument `%s`\n", argv[i]);
            return 1;
        }
    }

    static unsigned char hinein[VORRAT];
    for (long k = 0; k < VORRAT; k++) {
        hinein[k] = (unsigned char)(k * 31 + 7);
    }
    int roehre[2];
    if (pipe(roehre) != 0 || write(roehre[1], hinein, VORRAT) != VORRAT) {
        printf(KOPF);
        printf("      blind: pipe setup failed, errno=%d\n", errno);
        return 1;
    }

    /* Leg 1: at most len, the right bytes, nothing behind the window. */
    static unsigned char feld[FENSTER + WACHE];
    memset(feld, 0xA5, sizeof feld);
    long n = lies(roehre[0], feld, FENSTER);
    long grenze = kaputt ? FENSTER + 1 : FENSTER;
    int wache_heil = 1;
    for (int k = FENSTER; k < FENSTER + WACHE; k++) {
        if (feld[k] != 0xA5) {
            wache_heil = 0;
        }
    }
    if (kaputt) {
        printf(KOPF);
        printf("      control: window read answers %ld, demanded %ld -- detector falls\n", n,
               grenze);
        return 1;
    }
    if (n < 0 || n > FENSTER || memcmp(feld, hinein, (size_t)n) != 0 || !wache_heil) {
        printf(KOPF);
        printf("      REFUTED leg 1: read(len=%d) answered %ld, content %s, guard %s\n", FENSTER,
               n, (n >= 0 && n <= FENSTER && memcmp(feld, hinein, (size_t)n) == 0) ? "ok" : "differs",
               wache_heil ? "intact" : "WRITTEN");
        return 1;
    }

    long fenster_n = n;

    /* Leg 4 (needs the pipe): drain, close the write end, read 0. */
    static unsigned char rest[VORRAT];
    long weg = n;
    while (weg < VORRAT) {
        long m = lies(roehre[0], rest, sizeof rest);
        if (m <= 0) {
            break;
        }
        weg += m;
    }
    close(roehre[1]);
    long ende = lies(roehre[0], rest, sizeof rest);
    close(roehre[0]);
    if (weg != VORRAT || ende != 0) {
        printf(KOPF);
        printf("      REFUTED leg 4: drained %ld of %d, end of stream answered %ld\n", weg, VORRAT,
               ende);
        return 1;
    }

    /* Leg 2: EBADF. */
    errno = 0;
    n = lies(roehre[0], feld, FENSTER);
    int gesehen = errno;
    if (n != -1 || gesehen != EBADF) {
        printf(KOPF);
        printf("      REFUTED leg 2: closed-fd read answered %ld, errno=%d (want -1/EBADF=%d)\n",
               n, gesehen, EBADF);
        return 1;
    }

    /* Leg 3: EINVAL -- an eventfd counter is 8 bytes, a 4-byte read is invalid. */
    int ev = eventfd(1, 0);
    if (ev < 0) {
        printf(KOPF);
        printf("      blind: eventfd failed, errno=%d\n", errno);
        return 1;
    }
    errno = 0;
    n = lies(ev, feld, 4);
    gesehen = errno;
    close(ev);
    if (n != -1 || gesehen != EINVAL) {
        printf(KOPF);
        printf("      REFUTED leg 3: short eventfd read answered %ld, errno=%d (want -1/EINVAL=%d)\n",
               n, gesehen, EINVAL);
        return 1;
    }

    printf(KOPF);
    printf("      held: window read %ld <= %d with the right bytes and the guard intact, "
           "%d bytes drained then 0, EBADF and EINVAL observed\n", fenster_n, FENSTER, VORRAT);
    return 0;
}
#endif
