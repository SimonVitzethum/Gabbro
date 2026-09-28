/* messung/proben/os-bindung/melde.c -- the PROBE's own call into the operating
 * system (server lane, TODO section 0e K8).
 *
 * `os-probe.gab` declares `gabbro_probe_melde` with its shape, its effects, its
 * cost and the assumption this body has to keep (`os_probe_melde_vertrag`).
 * This file is that body, and `printf` stands HERE and nowhere else in the
 * probe.
 *
 * WHY IT MATTERS TO THE MEASUREMENT AND NOT ONLY TO THE RUN. The criterion of
 * `instrumente/pruefe-os-bindung.sh` is per OBJECT: the undefined symbols of the
 * linked binary that the RUNTIME's objects reference. A libc name the PROGRAM
 * pulls -- this `printf` -- must not be counted as the runtime's, and the only
 * thing that tells the two apart is which object holds the reference. So this
 * file is compiled on its own, exactly as `gabbro build` compiles a unit's
 * foreign bodies, and the probe would be measuring nothing if it were
 * `#include`d into the driver instead.
 */

#include <stdint.h>
#include <stdio.h>

void gabbro_probe_melde(uint32_t schluessel, uint64_t wert);

void gabbro_probe_melde(uint32_t schluessel, uint64_t wert)
{
    printf("k=%u v=%llu\n", (unsigned)schluessel, (unsigned long long)wert);
    fflush(stdout);
}
