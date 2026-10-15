/* sonde_open -- the falsifier for `linux_open_contract`.
 *
 * THE OBLIGATION, as it stands in the source (`beispiele/149-fd-offen.gab`):
 *
 *     assume linux_open_contract
 *         "Open keeps its contract on this machine: a descriptor that fits 32 bits, the mapped errnos."
 *         falsifier sonde_open;
 *
 * and at the syscall resting on it (`gate_open`, `abi linux arch x86_64 number 2`,
 * `regs in { rdi = path, rsi = flags, rdx = mode, r10 = pathlen }`,
 * `errors { ENOENT => NotFound, EACCES => Denied, EEXIST => Exists }`,
 * `ensures result <= 4294967295`).
 *
 * This probe belongs to EXACTLY this one obligation (N024). It was written by fix lane F5
 * (review G04 F4, 2026-09-22): until then the gate borrowed `linux_write_contract`, whose
 * probe only ever wrote into a pipe, so the open contract was named and never probed.
 *
 * WHAT IT MEASURES, AND WHAT IT DOES NOT ASSERT
 * ---------------------------------------------
 * The probe calls the same number the gate's stub loads (raw `syscall(2, ...)`, i.e.
 * `rax = 2` with the path in `rdi`, the flags in `rsi`, the mode in `rdx`), over a
 * NUL-terminated path -- the gate's named CALLER assumption `path_nul_terminated`, which
 * this probe honours and does not test:
 *
 *   1. a well-formed open answers a descriptor inside the carrier: `open("/dev/null",
 *      O_RDONLY)` returns a value in 0 .. 4294967295 (`ensures result <= 4294967295`),
 *      and the descriptor reads (a zero-byte read from `/dev/null` returns 0);
 *   2. `ENOENT` for a path that is not there (a name under a fresh `mkdtemp` directory);
 *   3. `EEXIST` for `O_CREAT | O_EXCL` over an existing file (the probe's own);
 *   4. `EACCES` for a mode-0 file the probe made -- only where the probe is not privileged
 *      (as root the kernel grants it, and the leg says so instead of claiming a result).
 *
 * What it does NOT assert: the NUL (the caller's, by name), timing (no date is declared),
 * the unmapped errnos (they are the stub's hardware outcome, by construction), and any
 * filesystem but the bench's own temporary directory.
 *
 * POSITIVE CONTROL (R14)
 * ----------------------
 * `--kaputt` demands the wrong answer on leg 2 (a SUCCESS for the missing path) and must
 * exit 1. A detector that cannot go red is a reassurance, not a probe.
 *
 * Documented runs (cc -std=c11 -O2 -Wall -Wextra -Werror, x86_64 Linux, 2026-09-22):
 *   $ ./sonde_open            -> exit 0 (PASSES)
 *   $ ./sonde_open --kaputt   -> exit 1 (control FALLS)
 *
 * Contract (`sonden/README.md`):
 *     0    not refuted in this run   -- and that is ALL it means
 *     1    REFUTED, or the probe showed itself blind
 *     77   not runnable here -- no Linux x86_64 userland on this machine
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define KOPF "sonde sonde_open :: linux_open_contract (beispiele/149-fd-offen.gab)\n"

#if !defined(__linux__) || !defined(__x86_64__)
int main(void)
{
    printf(KOPF);
    printf("      no Linux x86_64 userland on this machine -- not runnable here\n");
    return 77;
}
#else

/* The gate's own call: number 2, three argument registers. */
static long oeffne(const char *pfad, long flags, long modus)
{
    return syscall(2, pfad, flags, modus);
}

int main(int argc, char **argv)
{
    int kaputt = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--kaputt") == 0) {
            kaputt = 1;
        } else if (strcmp(argv[i], "--runden") == 0 && i + 1 < argc) {
            i++; /* the runner's round count: one open per leg is the whole measurement */
        } else if (argv[i][0] >= '0' && argv[i][0] <= '9') {
            /* the runner passes its round count bare */
        } else {
            printf(KOPF);
            printf("      misuse: unknown argument `%s`\n", argv[i]);
            return 1;
        }
    }

    /* Leg 1: a descriptor inside the carrier, and it reads. */
    errno = 0;
    long fd = oeffne("/dev/null", O_RDONLY, 0);
    if (fd < 0 || fd > 4294967295L) {
        printf(KOPF);
        printf("      REFUTED leg 1: open(/dev/null) answered %ld, errno=%d\n", fd, errno);
        return 1;
    }
    char b;
    if (read((int)fd, &b, 0) != 0) {
        printf(KOPF);
        printf("      REFUTED leg 1: the answered descriptor %ld does not read\n", fd);
        return 1;
    }
    close((int)fd);

    char verz[] = "/tmp/sonde_open_XXXXXX";
    if (mkdtemp(verz) == NULL) {
        printf(KOPF);
        printf("      blind: mkdtemp failed, errno=%d\n", errno);
        return 1;
    }
    char fehlt[256], da[256], zu[256];
    snprintf(fehlt, sizeof fehlt, "%s/fehlt", verz);
    snprintf(da, sizeof da, "%s/da", verz);
    snprintf(zu, sizeof zu, "%s/zu", verz);
    int urteil = 0;

    /* Leg 2: ENOENT. */
    errno = 0;
    long r = oeffne(fehlt, O_RDONLY, 0);
    int gesehen = errno;
    if (kaputt) {
        printf(KOPF);
        printf("      control: missing path answers %ld/errno=%d, demanded success -- detector falls\n",
               r, gesehen);
        urteil = 1;
        goto aufraeumen;
    }
    if (r != -1 || gesehen != ENOENT) {
        printf(KOPF);
        printf("      REFUTED leg 2: missing path answered %ld, errno=%d (want -1/ENOENT=%d)\n",
               r, gesehen, ENOENT);
        urteil = 1;
        goto aufraeumen;
    }

    /* Leg 3: EEXIST under O_CREAT|O_EXCL over the probe's own file. */
    long f = oeffne(da, O_CREAT | O_WRONLY, 0600);
    if (f < 0) {
        printf(KOPF);
        printf("      blind: could not create %s, errno=%d\n", da, errno);
        urteil = 1;
        goto aufraeumen;
    }
    close((int)f);
    errno = 0;
    r = oeffne(da, O_CREAT | O_EXCL | O_WRONLY, 0600);
    gesehen = errno;
    if (r != -1 || gesehen != EEXIST) {
        printf(KOPF);
        printf("      REFUTED leg 3: exclusive create answered %ld, errno=%d (want -1/EEXIST=%d)\n",
               r, gesehen, EEXIST);
        if (r >= 0) {
            close((int)r);
        }
        urteil = 1;
        goto aufraeumen;
    }

    /* Leg 4: EACCES over a mode-0 file, unprivileged only. */
    const char *leg4 = "EACCES observed";
    f = oeffne(zu, O_CREAT | O_WRONLY, 0);
    if (f < 0) {
        printf(KOPF);
        printf("      blind: could not create %s, errno=%d\n", zu, errno);
        urteil = 1;
        goto aufraeumen;
    }
    close((int)f);
    errno = 0;
    r = oeffne(zu, O_RDONLY, 0);
    gesehen = errno;
    if (geteuid() == 0) {
        leg4 = "EACCES leg not measurable as root (the kernel grants it)";
        if (r >= 0) {
            close((int)r);
        }
    } else if (r != -1 || gesehen != EACCES) {
        printf(KOPF);
        printf("      REFUTED leg 4: mode-0 file answered %ld, errno=%d (want -1/EACCES=%d)\n",
               r, gesehen, EACCES);
        if (r >= 0) {
            close((int)r);
        }
        urteil = 1;
        goto aufraeumen;
    }

    printf(KOPF);
    printf("      held: descriptor %ld in 0 .. 4294967295 and readable, ENOENT and EEXIST "
           "observed, %s\n", fd, leg4);

aufraeumen:
    unlink(da);
    unlink(zu);
    rmdir(verz);
    return urteil;
}
#endif
