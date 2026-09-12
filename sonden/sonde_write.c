/* sonde_write -- the falsifier for `linux_write_contract`.
 *
 * THE OBLIGATION, as it stands in the source (`beispiele/74-syscall-schreiben.gab`:22):
 *
 *     assume linux_write_contract
 *         "Write keeps its contract on this machine."
 *         falsifier sonde_write;
 *
 * and at the syscall resting on it (`beispiele/74-syscall-schreiben.gab`:35):
 *
 *     assume linux_write_contract falsifier sonde_write;
 *
 * This probe belongs to EXACTLY this one obligation (N024).
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * The contract has three legs, and the probe walks all three against the
 * bench's own kernel -- a pipe stands in for the descriptor the declaration
 * names, because a probe opens no user files and assumes no filesystem:
 *
 *   1. within the declared length the kernel writes what the registers name:
 *      1024 bytes into a pipe come back out byte-identical (`memcmp` over the
 *      read-back buffer), and the return value is 1024 (`result <= len`);
 *   2. the admitted errnos are answered: a write to a closed descriptor
 *      returns -1 with `errno == EBADF` (the `EBADF => BadFd` arm);
 *   3. the empty transfer: a zero-length write returns 0.
 *
 * What it does NOT assert: timing (no date is declared here), `EINTR` and
 * `EAGAIN` (no signal and no non-blocking descriptor stand on this bench --
 * those arms are covered by shape (`N061`), not by this run), and any
 * descriptor but a pipe.
 *
 * POSITIVE CONTROL (R14)
 * ----------------------
 * `--kaputt` demands the wrong answer on the good path (return == len + 1)
 * and must exit 1. A detector that cannot go red is a reassurance, not a
 * probe. The default run must pass (exit 0).
 *
 * Documented runs (cc -std=c11 -O2 -Wall -Wextra -Werror, x86_64 Linux):
 *   $ ./sonde_write
 *     -> exit 0, 1024/1024 bytes round-tripped, EBADF observed (PASSES)
 *   $ ./sonde_write --kaputt
 *     -> exit 1, good path answers 1024, demanded 1025 (control FALLS)
 *
 * Contract (`sonden/README.md`):
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no Linux userland on this machine
 */
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#if !defined(__linux__)
int main(void)
{
    printf("sonde sonde_write :: linux_write_contract "
           "(beispiele/74-syscall-schreiben.gab:22)\n");
    printf("      no Linux userland on this machine -- not runnable here\n");
    return 77;
}
#else

#define LAENGE 1024L
#define STANDARD_RUNDEN 20000L
#define MAX_RUNDEN 200000L

static long dezimal(const char *s, long *aus)
{
    long v = 0;
    if (*s == '\0') {
        return -1;
    }
    for (; *s; s++) {
        if (*s < '0' || *s > '9') {
            return -1;
        }
        v = v * 10 + (*s - '0');
        if (v > 100 * MAX_RUNDEN) {
            return -1;
        }
    }
    /* The runner passes its round count bare (2000000); the cap below is the
     * same favour the date probes grant it -- run the capped window, loudly. */
    *aus = v > MAX_RUNDEN ? MAX_RUNDEN : v;
    return 0;
}

int main(int argc, char **argv)
{
    long runden = STANDARD_RUNDEN;
    int kaputt = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--kaputt") == 0) {
            kaputt = 1;
        } else if (strcmp(argv[i], "--runden") == 0 && i + 1 < argc) {
            if (dezimal(argv[++i], &runden) != 0 || runden < 1) {
                printf("sonde sonde_write :: linux_write_contract\n");
                printf("      misuse: --runden needs 1..%ld\n", MAX_RUNDEN);
                return 1;
            }
        } else if (dezimal(argv[i], &runden) != 0 || runden < 1) {
            /* The runner passes its round count bare. Anything else is misuse,
             * and misuse is loud (exit 1), never a silent default. */
            printf("sonde sonde_write :: linux_write_contract\n");
            printf("      misuse: unknown argument `%s`\n", argv[i]);
            return 1;
        }
    }

    static unsigned char hinein[LAENGE];
    static unsigned char heraus[LAENGE];
    for (long k = 0; k < LAENGE; k++) {
        hinein[k] = (unsigned char)(k * 31 + 7);
    }

    int roehre[2];
    if (pipe(roehre) != 0) {
        printf("sonde sonde_write :: linux_write_contract "
               "(beispiele/74-syscall-schreiben.gab:22)\n");
        printf("      blind: pipe() failed, errno=%d\n", errno);
        return 1;
    }

    /* Leg 1: the full transfer, content and count. */
    long geschrieben_insgesamt = 0;
    for (long r = 0; r < runden; r++) {
        ssize_t n = write(roehre[1], hinein, (size_t)LAENGE);
        if (n != LAENGE) {
            printf("sonde sonde_write :: linux_write_contract "
                   "(beispiele/74-syscall-schreiben.gab:22)\n");
            printf("      REFUTED leg 1: write returned %ld of %ld\n",
                   (long)n, LAENGE);
            return 1;
        }
        geschrieben_insgesamt += (long)n;
        ssize_t m = read(roehre[0], heraus, (size_t)LAENGE);
        if (m != LAENGE || memcmp(hinein, heraus, (size_t)LAENGE) != 0) {
            printf("sonde sonde_write :: linux_write_contract "
                   "(beispiele/74-syscall-schreiben.gab:22)\n");
            printf("      REFUTED leg 1: read back %ld bytes, content %s\n",
                   (long)m, m == LAENGE ? "differs" : "short");
            return 1;
        }
    }
    if (kaputt) {
        /* The positive control: demand the wrong answer on the good path. */
        printf("sonde sonde_write :: linux_write_contract "
               "(beispiele/74-syscall-schreiben.gab:22)\n");
        printf("      control: good path answers %ld, demanded %ld -- detector falls\n",
               LAENGE, LAENGE + 1);
        return 1;
    }

    /* Leg 2: the admitted errno is answered. */
    close(roehre[1]);
    close(roehre[0]);
    errno = 0;
    ssize_t n = write(-1, hinein, (size_t)LAENGE);
    int gesehen = errno;
    if (n != -1 || gesehen != EBADF) {
        printf("sonde sonde_write :: linux_write_contract "
               "(beispiele/74-syscall-schreiben.gab:22)\n");
        printf("      REFUTED leg 2: bad-fd write returned %ld, errno=%d (want -1/EBADF=%d)\n",
               (long)n, gesehen, EBADF);
        return 1;
    }

    /* Leg 3: the empty transfer. */
    if (pipe(roehre) != 0) {
        printf("sonde sonde_write :: linux_write_contract "
               "(beispiele/74-syscall-schreiben.gab:22)\n");
        printf("      blind: pipe() failed, errno=%d\n", errno);
        return 1;
    }
    n = write(roehre[1], hinein, 0);
    if (n != 0) {
        printf("sonde sonde_write :: linux_write_contract "
               "(beispiele/74-syscall-schreiben.gab:22)\n");
        printf("      REFUTED leg 3: zero-length write returned %ld\n", (long)n);
        return 1;
    }
    close(roehre[1]);
    close(roehre[0]);

    printf("sonde sonde_write :: linux_write_contract "
           "(beispiele/74-syscall-schreiben.gab:22)\n");
    printf("      held over %ld rounds: %ld bytes round-tripped, "
           "EBADF observed, empty transfer 0\n",
           runden, geschrieben_insgesamt);
    return 0;
}
#endif
